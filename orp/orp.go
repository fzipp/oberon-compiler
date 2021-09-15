// N. Wirth 1.7.97 / 8.3.2020  Oberon compiler for RISC in Oberon-07
// Author: Niklaus Wirth, 2014.
// Ported from Oberon to Go by Frederik Zipp, 2021.

// Package orp contains the parser for the Oberon RISC compiler.
package orp

import (
	"fmt"
	"io"
	"os"

	"github.com/fzipp/oberon-compiler/orb"
	"github.com/fzipp/oberon-compiler/org"
	"github.com/fzipp/oberon-compiler/ors"
)

// Parser of Oberon-RISC compiler. Uses Scanner ORS to obtain symbols (tokens),
// ORB for definition of data structures and for handling import and export,
// and Generator ORG to produce binary code. ORP performs type checking and
// data allocation. Parser is target-independent, except for part of the
// handling of allocations.
type Parser struct {
	ors *ors.Scanner
	orb *orb.Base
	org *org.Generator

	sym     ors.Sym // last symbol read
	dc      int32   // data counter
	level   int32
	exNo    int32
	version int32
	newSF   bool // option flag: new symbol file?
	modId   ors.Ident
	pbsList []*ptrBase
	dummy   *orb.Object
	w       io.Writer
}

type ptrBase struct {
	name ors.Ident
	typ  *orb.Type
}

func NewParser(s *ors.Scanner, b *orb.Base, g *org.Generator, w io.Writer) *Parser {
	return &Parser{
		ors: s, orb: b, org: g,
		dummy: &orb.Object{
			Class: orb.ClassVar,
			Type:  b.IntType,
		},
		w: w,
	}
}

func (p *Parser) nextSym() {
	p.sym = p.ors.Get()
}

func (p *Parser) check(s ors.Sym, msg string) {
	if p.sym == s {
		p.nextSym()
	} else {
		p.ors.Mark(msg)
	}
}

func (p *Parser) qualIdent() *orb.Object {
	obj := p.orb.ThisObj()
	p.nextSym()
	if obj == nil {
		p.ors.Mark("undef")
		obj = p.dummy
	}
	if p.sym == ors.SymPeriod && obj.Class == orb.ClassMod {
		p.nextSym()
		if p.sym == ors.SymIdent {
			obj = p.orb.ThisImport(obj)
			p.nextSym()
			if obj == nil {
				p.ors.Mark("undef")
				obj = p.dummy
			}
		} else {
			p.ors.Mark("identifier expected")
			obj = p.dummy
		}
	}
	return obj
}

func (p *Parser) checkBool(x *org.Item) {
	if x.Type.Form != orb.FormBool {
		p.ors.Mark("not Boolean")
		x.Type = p.orb.BoolType
	}
}

func (p *Parser) checkInt(x *org.Item) {
	if x.Type.Form != orb.FormInt {
		p.ors.Mark("not integer")
		x.Type = p.orb.IntType
	}
}

func (p *Parser) checkReal(x *org.Item) {
	if x.Type.Form != orb.FormReal {
		p.ors.Mark("not Real")
		x.Type = p.orb.RealType
	}
}

func (p *Parser) checkSet(x *org.Item) {
	if x.Type.Form != orb.FormSet {
		p.ors.Mark("not Set")
		x.Type = p.orb.SetType
	}
}

func (p *Parser) checkSetVal(x *org.Item) {
	if x.Type.Form != orb.FormInt {
		p.ors.Mark("not Int")
		x.Type = p.orb.SetType
	} else if x.Mode == orb.ClassConst {
		if x.A < 0 || x.A >= 32 {
			p.ors.Mark("invalid set")
		}
	}
}

func (p *Parser) checkConst(x *org.Item) {
	if x.Mode != orb.ClassConst {
		p.ors.Mark("not a constant")
		x.Mode = orb.ClassConst
	}
}

func (p *Parser) checkReadOnly(x *org.Item) {
	if x.Rdo {
		p.ors.Mark("read-only")
	}
}

func (p *Parser) checkExport() (expo bool) {
	if p.sym == ors.SymTimes {
		expo = true
		p.nextSym()
		if p.level != 0 {
			p.ors.Mark("remove asterisk")
		}
	} else {
		expo = false
	}
	return expo
}

func isExtension(t0, t1 *orb.Type) bool {
	// t1 is an extension of t0
	return (t0 == t1) || (t1 != nil && isExtension(t0, t1.Base))
}

// expressions

func (p *Parser) typeTest(x *org.Item, t *orb.Type, guard bool) {
	xt := x.Type
	if (t.Form == xt.Form) && ((t.Form == orb.FormPointer) || (t.Form == orb.FormRecord && x.Mode == orb.ClassPar)) {
		for xt != t && xt != nil {
			xt = xt.Base
		}
		if xt != t {
			xt = x.Type
			if xt.Form == orb.FormPointer {
				if isExtension(xt.Base, t.Base) {
					p.org.TypeTest(x, t.Base, false, guard)
					x.Type = t
				} else {
					p.ors.Mark("not an extension")
				}
			} else if xt.Form == orb.FormRecord && x.Mode == orb.ClassPar {
				if isExtension(xt, t) {
					p.org.TypeTest(x, t, true, guard)
					x.Type = t
				} else {
					p.ors.Mark("not an extension")
				}
			} else {
				p.ors.Mark("incompatible types")
			}
		} else if !guard {
			p.org.TypeTest(x, nil, false, false)
		}
	} else {
		p.ors.Mark("type mismatch")
	}
	if !guard {
		x.Type = p.orb.BoolType
	}
}

func (p *Parser) selector(x *org.Item) {
	for p.sym == ors.SymLbrak || p.sym == ors.SymPeriod || p.sym == ors.SymArrow ||
		(p.sym == ors.SymLparen && (x.Type.Form == orb.FormRecord || x.Type.Form == orb.FormPointer)) {

		if p.sym == ors.SymLbrak {
			for {
				p.nextSym()
				var y org.Item
				p.expression(&y)
				if x.Type.Form == orb.FormArray {
					p.checkInt(&y)
					p.org.Index(x, &y)
					x.Type = x.Type.Base
				} else {
					p.ors.Mark("not an array")
				}
				if p.sym != ors.SymComma {
					break
				}
			}
			p.check(ors.SymRbrak, "no ]")
		} else if p.sym == ors.SymPeriod {
			p.nextSym()
			if p.sym == ors.SymIdent {
				if x.Type.Form == orb.FormPointer {
					p.org.DeRef(x)
					x.Type = x.Type.Base
				}
				if x.Type.Form == orb.FormRecord {
					obj := p.orb.ThisField(x.Type)
					p.nextSym()
					if obj != nil {
						p.org.Field(x, obj)
						x.Type = obj.Type
					} else {
						p.ors.Mark("undef")
					}
				} else {
					p.ors.Mark("not a record")
				}
			} else {
				p.ors.Mark("ident?")
			}
		} else if p.sym == ors.SymArrow {
			p.nextSym()
			if x.Type.Form == orb.FormPointer {
				p.org.DeRef(x)
				x.Type = x.Type.Base
			} else {
				p.ors.Mark("not a pointer")
			}
		} else if p.sym == ors.SymLparen && (x.Type.Form == orb.FormRecord || x.Type.Form == orb.FormPointer) {
			// type guard
			p.nextSym()
			if p.sym == ors.SymIdent {
				obj := p.qualIdent()
				if obj.Class == orb.ClassTyp {
					p.typeTest(x, obj.Type, true)
				} else {
					p.ors.Mark("guard type expected")
				}
			} else {
				p.ors.Mark("not an identifier")
			}
			p.check(ors.SymRparen, " ) missing")
		}
	}
}

func equalSignatures(t0, t1 *orb.Type) (com bool) {
	com = true
	if (t0.Base == t1.Base) && (t0.NOfPar == t1.NOfPar) {
		p0 := t0.Dsc
		p1 := t1.Dsc
		for p0 != nil {
			if (p0.Class == p1.Class) && (p0.Rdo == p1.Rdo) && ((p0.Type == p1.Type) ||
				((p0.Type.Form == orb.FormArray) && (p1.Type.Form == orb.FormArray) && (p0.Type.Len == p1.Type.Len) && (p0.Type.Base == p1.Type.Base)) ||
				((p0.Type.Form == orb.FormProc) && (p1.Type.Form == orb.FormProc) && equalSignatures(p0.Type, p1.Type))) {

				p0 = p0.Next
				p1 = p1.Next
			} else {
				p0 = nil
				com = false
			}
		}
	} else {
		com = false
	}
	return com
}

func (p *Parser) compTypes(t0, t1 *orb.Type, varPar bool) bool {
	// check for assignment compatibility
	return (t0 == t1) || // open array assignment disallowed in ORG
		(t0.Form == orb.FormArray) && (t1.Form == orb.FormArray) && (t0.Base == t1.Base) && (t0.Len == t1.Len) ||
		(t0.Form == orb.FormRecord) && (t1.Form == orb.FormRecord) && isExtension(t0, t1) ||
		!varPar && ((t0.Form == orb.FormPointer) && (t1.Form == orb.FormPointer) && isExtension(t0.Base, t1.Base) ||
			(t0.Form == orb.FormProc) && (t1.Form == orb.FormProc) && equalSignatures(t0, t1) ||
			(t0.Form == orb.FormPointer || t0.Form == orb.FormProc) && (t1.Form == orb.FormNilTyp))
}

func (p *Parser) parameter(par *orb.Object) {
	var x org.Item
	p.expression(&x)
	if par != nil {
		varPar := par.Class == orb.ClassPar
		if p.compTypes(par.Type, x.Type, varPar) {
			if !varPar {
				p.org.ValueParam(&x)
			} else {
				// par.Class == ClassPar
				if !par.Rdo {
					p.checkReadOnly(&x)
				}
				p.org.VarParam(&x, par.Type)
			}
		} else if (x.Type.Form == orb.FormArray) && (par.Type.Form == orb.FormArray) &&
			(x.Type.Base == par.Type.Base) && (par.Type.Len < 0) {

			if !par.Rdo {
				p.checkReadOnly(&x)
			}
			p.org.OpenArrayParam(&x)
		} else if (x.Type.Form == orb.FormString) && varPar && par.Rdo && (par.Type.Form == orb.FormArray) &&
			(par.Type.Base.Form == orb.FormChar) && (par.Type.Len < 0) {

			p.org.StringParam(&x)
		} else if !varPar && (par.Type.Form == orb.FormInt) && (x.Type.Form == orb.FormInt) {
			p.org.ValueParam(&x) // BYTE
		} else if (x.Type.Form == orb.FormString) && (x.B == 2) && (par.Class == orb.ClassVar) && (par.Type.Form == orb.FormChar) {
			p.org.StrToChar(&x)
			p.org.ValueParam(&x)
		} else if (par.Type.Form == orb.FormArray) && (par.Type.Base == p.orb.ByteType) &&
			(par.Type.Len >= 0) && (par.Type.Size == x.Type.Size) {

			p.org.VarParam(&x, par.Type)
		} else {
			p.ors.Mark("incompatible parameters")
		}
	}
}

func (p *Parser) paramList(x *org.Item) {
	par := x.Type.Dsc
	n := int32(0)
	if p.sym != ors.SymRparen {
		p.parameter(par)
		n = 1
		for p.sym <= ors.SymComma {
			p.check(ors.SymComma, "comma?")
			if par != nil {
				par = par.Next
			}
			n++
			p.parameter(par)
		}
		p.check(ors.SymRparen, ") missing")
	} else {
		p.nextSym()
	}
	if n < x.Type.NOfPar {
		p.ors.Mark("too few params")
	} else if n > x.Type.NOfPar {
		p.ors.Mark("too many params")
	}
}

func (p *Parser) standFunc(x *org.Item, fct int32, resTyp *orb.Type) {
	var y org.Item
	p.check(ors.SymLparen, "no (")
	nPar := fct % 10
	fct = fct / 10
	p.expression(x)
	n := int32(1)
	for p.sym == ors.SymComma {
		p.nextSym()
		p.expression(&y)
		n++
	}
	p.check(ors.SymRparen, "no )")
	if n == nPar {
		switch fct {
		case 0: // ABS
			if (x.Type.Form == orb.FormInt) || (x.Type.Form == orb.FormReal) {
				p.org.Abs(x)
				resTyp = x.Type
			} else {
				p.ors.Mark("bad type")
			}
		case 1: // ODD
			p.checkInt(x)
			p.org.Odd(x)
		case 2: // FLOOR
			p.checkReal(x)
			p.org.Floor(x)
		case 3: // FLT
			p.checkInt(x)
			p.org.Float(x)
		case 4: // ORD
			if x.Type.Form <= orb.FormProc {
				p.org.Ord(x)
			} else if (x.Type.Form == orb.FormString) && (x.B == 2) {
				p.org.StrToChar(x)
			} else {
				p.ors.Mark("bad type")
			}
		case 5: // CHR
			p.checkInt(x)
			p.org.Ord(x)
		case 6: // LEN
			if x.Type.Form == orb.FormArray {
				p.org.Len(x)
			} else {
				p.ors.Mark("not an array")
			}
		case 7, 8, 9: // LSL, ASR, ROR
			p.checkInt(&y)
			if (x.Type.Form == orb.FormInt) || (x.Type.Form == orb.FormSet) {
				p.org.Shift(fct-7, x, &y)
				resTyp = x.Type
			} else {
				p.ors.Mark("bad type")
			}
		case 11: // ADC
			p.org.ADC(x, &y)
		case 12: // SBC
			p.org.SBC(x, &y)
		case 13: // UML
			p.org.UML(x, &y)
		case 14: // BIT
			p.checkInt(x)
			p.checkInt(&y)
			p.org.Bit(x, &y)
		case 15: // REG
			p.checkConst(x)
			p.checkInt(x)
			p.org.Register(x)
		case 16: // VAL
			if (x.Mode == orb.ClassTyp) && (x.Type.Size <= y.Type.Size) {
				resTyp = x.Type
				*x = y
			} else {
				p.ors.Mark("casting not allowed")
			}
		case 17: // ADR
			p.org.Adr(x)
		case 18: // SIZE
			if x.Mode == orb.ClassTyp {
				p.org.MakeConstItem(x, p.orb.IntType, x.Type.Size)
			} else {
				p.ors.Mark("must be a type")
			}
		case 19: // COND
			p.checkConst(x)
			p.checkInt(x)
			p.org.Condition(x)
		case 20: // H
			p.checkConst(x)
			p.checkInt(x)
			p.org.H(x)
		}
		x.Type = resTyp
	} else {
		p.ors.Mark("wrong nof params")
	}
}

func (p *Parser) element(x *org.Item) {
	p.expression(x)
	p.checkSetVal(x)
	if p.sym == ors.SymUpto {
		p.nextSym()
		var y org.Item
		p.expression(&y)
		p.checkSetVal(&y)
		p.org.Set(x, &y)
	} else {
		p.org.Singleton(x)
	}
	x.Type = p.orb.SetType
}

func (p *Parser) set(x *org.Item) {
	if p.sym >= ors.SymIf {
		if p.sym != ors.SymRbrace {
			p.ors.Mark(" } missing")
		}
		p.org.MakeConstItem(x, p.orb.SetType, 0) // empty set
	} else {
		p.element(x)
		for p.sym < ors.SymRparen || p.sym > ors.SymRbrace {
			if p.sym == ors.SymComma {
				p.nextSym()
			} else if p.sym != ors.SymRbrace {
				p.ors.Mark("missing comma")
			}
			var y org.Item
			p.element(&y)
			p.org.SetOp(ors.SymPlus, x, &y)
		}
	}
}

func (p *Parser) factor(x *org.Item) {
	if p.sym < ors.SymChar || p.sym > ors.SymIdent {
		p.ors.Mark("expression expected")
		for {
			p.nextSym()
			if (p.sym >= ors.SymChar && p.sym <= ors.SymFor) || (p.sym >= ors.SymThen) {
				break
			}
		}
	}
	if p.sym == ors.SymIdent {
		obj := p.qualIdent()
		if obj.Class == orb.ClassSFunc {
			p.standFunc(x, obj.Val, obj.Type)
		} else {
			p.org.MakeItem(x, obj, p.level)
			p.selector(x)
			if p.sym == ors.SymLparen {
				p.nextSym()
				if (x.Type.Form == orb.FormProc) && (x.Type.Base.Form != orb.FormNoTyp) {
					rx := p.org.PrepCall(x)
					p.paramList(x)
					p.org.Call(x, rx)
					x.Type = x.Type.Base
				} else {
					p.ors.Mark("not a function")
					p.paramList(x)
				}
			}
		}
	} else if p.sym == ors.SymInt {
		p.org.MakeConstItem(x, p.orb.IntType, p.ors.Ival)
		p.nextSym()
	} else if p.sym == ors.SymReal {
		p.org.MakeRealItem(x, p.ors.Rval)
		p.nextSym()
	} else if p.sym == ors.SymChar {
		p.org.MakeConstItem(x, p.orb.CharType, p.ors.Ival)
		p.nextSym()
	} else if p.sym == ors.SymNil {
		p.nextSym()
		p.org.MakeConstItem(x, p.orb.NilType, 0)
	} else if p.sym == ors.SymString {
		p.org.MakeStringItem(x, int32(len(p.ors.Str)))
		p.nextSym()
	} else if p.sym == ors.SymLparen {
		p.nextSym()
		p.expression(x)
		p.check(ors.SymRparen, "no )")
	} else if p.sym == ors.SymLbrace {
		p.nextSym()
		p.set(x)
		p.check(ors.SymRbrace, "no }")
	} else if p.sym == ors.SymNot {
		p.nextSym()
		p.factor(x)
		p.checkBool(x)
		p.org.Not(x)
	} else if p.sym == ors.SymFalse {
		p.nextSym()
		p.org.MakeConstItem(x, p.orb.BoolType, 0)
	} else if p.sym == ors.SymTrue {
		p.nextSym()
		p.org.MakeConstItem(x, p.orb.BoolType, 1)
	} else {
		p.ors.Mark("not a factor")
		p.org.MakeConstItem(x, p.orb.IntType, 0)
	}
}

func (p *Parser) term(x *org.Item) {
	var y org.Item
	p.factor(x)
	f := x.Type.Form
	for p.sym >= ors.SymTimes && p.sym <= ors.SymAnd {
		op := p.sym
		p.nextSym()
		if op == ors.SymTimes {
			if f == orb.FormInt {
				p.factor(&y)
				p.checkInt(&y)
				p.org.MulOp(x, &y)
			} else if f == orb.FormReal {
				p.factor(&y)
				p.checkReal(&y)
				p.org.RealOp(op, x, &y)
			} else if f == orb.FormSet {
				p.factor(&y)
				p.checkSet(&y)
				p.org.SetOp(op, x, &y)
			} else {
				p.ors.Mark("bad type")
			}
		} else if op == ors.SymDiv || op == ors.SymMod {
			p.checkInt(x)
			p.factor(&y)
			p.checkInt(&y)
			p.org.DivOp(op, x, &y)
		} else if op == ors.SymRdiv {
			if f == orb.FormReal {
				p.factor(&y)
				p.checkReal(&y)
				p.org.RealOp(op, x, &y)
			} else if f == orb.FormSet {
				p.factor(&y)
				p.checkSet(&y)
				p.org.SetOp(op, x, &y)
			} else {
				p.ors.Mark("bad type")
			}
		} else {
			// op == SymAnd
			p.checkBool(x)
			p.org.And1(x)
			p.factor(&y)
			p.checkBool(&y)
			p.org.And2(x, &y)
		}
	}
}

func (p *Parser) simpleExpression(x *org.Item) {
	var y org.Item
	if p.sym == ors.SymMinus {
		p.nextSym()
		p.term(x)
		if x.Type.Form == orb.FormInt || x.Type.Form == orb.FormReal || x.Type.Form == orb.FormSet {
			p.org.Neg(x)
		} else {
			p.checkInt(x)
		}
	} else if p.sym == ors.SymPlus {
		p.nextSym()
		p.term(x)
	} else {
		p.term(x)
	}
	for p.sym >= ors.SymPlus && p.sym <= ors.SymOr {
		op := p.sym
		p.nextSym()
		if op == ors.SymOr {
			p.org.Or1(x)
			p.checkBool(x)
			p.term(&y)
			p.checkBool(&y)
			p.org.Or2(x, &y)
		} else if x.Type.Form == orb.FormInt {
			p.term(&y)
			p.checkInt(&y)
			p.org.AddOp(op, x, &y)
		} else if x.Type.Form == orb.FormReal {
			p.term(&y)
			p.checkReal(&y)
			p.org.RealOp(op, x, &y)
		} else {
			p.checkSet(x)
			p.term(&y)
			p.checkSet(&y)
			p.org.SetOp(op, x, &y)
		}
	}
}

func (p *Parser) expression(x *org.Item) {
	var y org.Item
	p.simpleExpression(x)
	if (p.sym >= ors.SymEql) && (p.sym <= ors.SymGeq) {
		rel := p.sym
		p.nextSym()
		p.simpleExpression(&y)
		xf := x.Type.Form
		yf := y.Type.Form
		if x.Type == y.Type {
			if xf == orb.FormChar || xf == orb.FormInt {
				p.org.IntRelation(rel, x, &y)
			} else if xf == orb.FormReal {
				p.org.RealRelation(rel, x, &y)
			} else if xf == orb.FormSet || xf == orb.FormPointer || xf == orb.FormProc || xf == orb.FormNilTyp || xf == orb.FormBool {
				if rel <= ors.SymNeq {
					p.org.IntRelation(rel, x, &y)
				} else {
					p.ors.Mark("only = or #")
				}
			} else if (xf == orb.FormArray && x.Type.Base.Form == orb.FormChar) || xf == orb.FormString {
				p.org.StringRelation(rel, x, &y)
			} else {
				p.ors.Mark("illegal comparison")
			}
		} else if ((xf == orb.FormPointer || xf == orb.FormProc) && yf == orb.FormNilTyp) ||
			((yf == orb.FormPointer || yf == orb.FormProc) && xf == orb.FormNilTyp) {

			if rel <= ors.SymNeq {
				p.org.IntRelation(rel, x, &y)
			} else {
				p.ors.Mark("only = or #")
			}
		} else if (xf == orb.FormPointer && yf == orb.FormPointer && (isExtension(x.Type.Base, y.Type.Base) || isExtension(y.Type.Base, x.Type.Base))) ||
			(xf == orb.FormProc && yf == orb.FormProc && equalSignatures(x.Type, y.Type)) {

			if rel <= ors.SymNeq {
				p.org.IntRelation(rel, x, &y)
			} else {
				p.ors.Mark("only = or #")
			}
		} else if (xf == orb.FormArray && x.Type.Base.Form == orb.FormChar && (yf == orb.FormString || (yf == orb.FormArray && y.Type.Base.Form == orb.FormChar))) ||
			(yf == orb.FormArray && y.Type.Base.Form == orb.FormChar && xf == orb.FormString) {

			p.org.StringRelation(rel, x, &y)
		} else if xf == orb.FormChar && yf == orb.FormString && y.B == 2 {
			p.org.StrToChar(&y)
			p.org.IntRelation(rel, x, &y)
		} else if yf == orb.FormChar && xf == orb.FormString && x.B == 2 {
			p.org.StrToChar(x)
			p.org.IntRelation(rel, x, &y)
		} else if xf == orb.FormInt && yf == orb.FormInt {
			p.org.IntRelation(rel, x, &y) // BYTE
		} else {
			p.ors.Mark("illegal comparison")
		}
		x.Type = p.orb.BoolType
	} else if p.sym == ors.SymIn {
		p.nextSym()
		p.checkInt(x)
		p.simpleExpression(&y)
		p.checkSet(&y)
		p.org.In(x, &y)
		x.Type = p.orb.BoolType
	} else if p.sym == ors.SymIs {
		p.nextSym()
		obj := p.qualIdent()
		p.typeTest(x, obj.Type, false)
		x.Type = p.orb.BoolType
	}
}

// statements

func (p *Parser) standProc(pno int32) {
	p.check(ors.SymLparen, "no (")
	nPar := pno % 10
	pno = pno / 10
	var x, y, z org.Item
	p.expression(&x)
	nap := int32(1)
	if p.sym == ors.SymComma {
		p.nextSym()
		p.expression(&y)
		nap = 2
		z.Type = p.orb.NoType
		for p.sym == ors.SymComma {
			p.nextSym()
			p.expression(&z)
			nap++
		}
	} else {
		y.Type = p.orb.NoType
	}
	p.check(ors.SymRparen, "no )")
	if (nPar == nap) || (pno == 0 || pno == 1) {
		switch pno {
		case 0, 1: // INC, DEC
			p.checkInt(&x)
			p.checkReadOnly(&x)
			if y.Type != p.orb.NoType {
				p.checkInt(&y)
			}
			p.org.Increment(pno, &x, &y)
		case 2, 3: // INCL, EXCL
			p.checkSet(&x)
			p.checkReadOnly(&x)
			p.checkInt(&y)
			p.org.Include(pno-2, &x, &y)
		case 4:
			p.checkBool(&x)
			p.org.Assert(&x)
		case 5: // NEW
			p.checkReadOnly(&x)
			if (x.Type.Form == orb.FormPointer) && (x.Type.Base.Form == orb.FormRecord) {
				p.org.New(&x)
			} else {
				p.ors.Mark("not a pointer to record")
			}
		case 6:
			p.checkReal(&x)
			p.checkInt(&y)
			p.checkReadOnly(&x)
			p.org.Pack(&x, &y)
		case 7:
			p.checkReal(&x)
			p.checkInt(&y)
			p.checkReadOnly(&x)
			p.org.Unpk(&x, &y)
		case 8:
			if x.Type.Form <= orb.FormSet {
				p.org.Led(&x)
			} else {
				p.ors.Mark("bad type")
			}
		case 10:
			p.checkInt(&x)
			p.org.Get(&x, &y)
		case 11:
			p.checkInt(&x)
			p.org.Put(&x, &y)
		case 12:
			p.checkInt(&x)
			p.checkInt(&y)
			p.checkInt(&z)
			p.org.Copy(&x, &y, &z)
		case 13:
			p.checkConst(&x)
			p.checkInt(&x)
			p.org.LDPSR(&x)
		case 14:
			p.checkInt(&x)
			p.org.LDREG(&x, &y)
		}
	} else {
		p.ors.Mark("wrong nof parameters")
	}
}

func (p *Parser) statSequence() {
	var x org.Item
	for {
		if !((p.sym >= ors.SymIdent) && (p.sym <= ors.SymFor) || (p.sym >= ors.SymSemicolon)) {
			p.ors.Mark("statement expected")
			for {
				p.nextSym()
				if p.sym >= ors.SymIdent {
					break
				}
			}
		}
		if p.sym == ors.SymIdent {
			obj := p.qualIdent()
			p.org.MakeItem(&x, obj, p.level)
			if x.Mode == orb.ClassSProc {
				p.standProc(obj.Val)
			} else {
				p.selector(&x)
				if p.sym == ors.SymBecomes {
					// assignment
					p.nextSym()
					p.checkReadOnly(&x)
					var y org.Item
					p.expression(&y)
					if p.compTypes(x.Type, y.Type, false) {
						if (x.Type.Form <= orb.FormPointer) || (x.Type.Form == orb.FormProc) {
							p.org.Store(&x, &y)
						} else {
							p.org.StoreStruct(&x, &y)
						}
					} else if (x.Type.Form == orb.FormArray) && (y.Type.Form == orb.FormArray) && (x.Type.Base == y.Type.Base) && (y.Type.Len < 0) {
						p.org.StoreStruct(&x, &y)
					} else if (x.Type.Form == orb.FormArray) && (x.Type.Base.Form == orb.FormChar) && (y.Type.Form == orb.FormString) {
						p.org.CopyString(&x, &y)
					} else if (x.Type.Form == orb.FormInt) && (y.Type.Form == orb.FormInt) {
						p.org.Store(&x, &y) // BYTE
					} else if (x.Type.Form == orb.FormChar) && (y.Type.Form == orb.FormString) && (y.B == 2) {
						p.org.StrToChar(&y)
						p.org.Store(&x, &y)
					} else {
						p.ors.Mark("illegal assignment")
					}
				} else if p.sym == ors.SymEql {
					p.ors.Mark("should be :=")
					p.nextSym()
					var y org.Item
					p.expression(&y)
				} else if p.sym == ors.SymLparen {
					// procedure call
					p.nextSym()
					if (x.Type.Form == orb.FormProc) && (x.Type.Base.Form == orb.FormNoTyp) {
						rx := p.org.PrepCall(&x)
						p.paramList(&x)
						p.org.Call(&x, rx)
					} else {
						p.ors.Mark("not a procedure")
						p.paramList(&x)
					}
				} else if x.Type.Form == orb.FormProc {
					// procedure call without parameters
					if x.Type.NOfPar > 0 {
						p.ors.Mark("missing parameters")
					}
					if x.Type.Base.Form == orb.FormNoTyp {
						rx := p.org.PrepCall(&x)
						p.org.Call(&x, rx)
					} else {
						p.ors.Mark("not a procedure")
					}
				} else if x.Mode == orb.ClassTyp {
					p.ors.Mark("illegal assignment")
				} else {
					p.ors.Mark("not a procedure")
				}
			}
		} else if p.sym == ors.SymIf {
			p.nextSym()
			p.expression(&x)
			p.checkBool(&x)
			p.org.CFJump(&x)
			p.check(ors.SymThen, "no THEN")
			p.statSequence()
			L0 := int32(0)
			for p.sym == ors.SymElsif {
				p.nextSym()
				p.org.FJump(&L0)
				p.org.Fixup(&x)
				p.expression(&x)
				p.checkBool(&x)
				p.org.CFJump(&x)
				p.check(ors.SymThen, "no THEN")
				p.statSequence()
			}
			if p.sym == ors.SymElse {
				p.nextSym()
				p.org.FJump(&L0)
				p.org.Fixup(&x)
				p.statSequence()
			} else {
				p.org.Fixup(&x)
			}
			p.org.FixLink(L0)
			p.check(ors.SymEnd, "no END")
		} else if p.sym == ors.SymWhile {
			p.nextSym()
			L0 := p.org.Here()
			p.expression(&x)
			p.checkBool(&x)
			p.org.CFJump(&x)
			p.check(ors.SymDo, "no DO")
			p.statSequence()
			p.org.BJump(L0)
			for p.sym == ors.SymElsif {
				p.nextSym()
				p.org.Fixup(&x)
				p.expression(&x)
				p.checkBool(&x)
				p.org.CFJump(&x)
				p.check(ors.SymDo, "no DO")
				p.statSequence()
				p.org.BJump(L0)
			}
			p.org.Fixup(&x)
			p.check(ors.SymEnd, "no END")
		} else if p.sym == ors.SymRepeat {
			p.nextSym()
			L0 := p.org.Here()
			p.statSequence()
			if p.sym == ors.SymUntil {
				p.nextSym()
				p.expression(&x)
				p.checkBool(&x)
				p.org.CBJump(&x, L0)
			} else {
				p.ors.Mark("missing UNTIL")
			}
		} else if p.sym == ors.SymFor {
			p.nextSym()
			if p.sym == ors.SymIdent {
				obj := p.qualIdent()
				p.org.MakeItem(&x, obj, p.level)
				p.checkInt(&x)
				p.checkReadOnly(&x)
				if p.sym == ors.SymBecomes {
					p.nextSym()
					var y org.Item
					p.expression(&y)
					p.checkInt(&y)
					p.org.For0(&x, &y)
					L0 := p.org.Here()
					p.check(ors.SymTo, "no TO")
					var z org.Item
					p.expression(&z)
					p.checkInt(&z)
					obj.Rdo = true
					var w org.Item
					if p.sym == ors.SymBy {
						p.nextSym()
						p.expression(&w)
						p.checkConst(&w)
						p.checkInt(&w)
					} else {
						p.org.MakeConstItem(&w, p.orb.IntType, 1)
					}
					p.check(ors.SymDo, "no DO")
					L1 := p.org.For1(&x, &y, &z, &w)
					p.statSequence()
					p.check(ors.SymEnd, "no END")
					p.org.For2(&x, &y, &w)
					p.org.BJump(L0)
					p.org.FixLink(L1)
					obj.Rdo = false
				} else {
					p.ors.Mark(":= expected")
				}
			} else {
				p.ors.Mark("identifier expected")
			}
		} else if p.sym == ors.SymCase {
			typeCase := func(obj *orb.Object, x *org.Item) {
				if p.sym == ors.SymIdent {
					typObj := p.qualIdent()
					p.org.MakeItem(x, obj, p.level)
					if typObj.Class != orb.ClassTyp {
						p.ors.Mark("not a type")
					}
					p.typeTest(x, typObj.Type, false)
					obj.Type = typObj.Type
					p.org.CFJump(x)
					p.check(ors.SymColon, ": expected")
					p.statSequence()
				} else {
					p.org.CFJump(x)
					p.ors.Mark("type id expected")
				}
			}
			skipCase := func() {
				for p.sym != ors.SymColon {
					p.nextSym()
				}
				p.nextSym()
				p.statSequence()
			}
			p.nextSym()
			if p.sym == ors.SymIdent {
				obj := p.qualIdent()
				orgType := obj.Type
				if (orgType.Form == orb.FormPointer) || ((orgType.Form == orb.FormRecord) && (obj.Class == orb.ClassPar)) {
					p.check(ors.SymOf, "OF expected")
					typeCase(obj, &x)
					L0 := int32(0)
					for p.sym == ors.SymBar {
						p.nextSym()
						p.org.FJump(&L0)
						p.org.Fixup(&x)
						obj.Type = orgType
						typeCase(obj, &x)
					}
					p.org.Fixup(&x)
					p.org.FixLink(L0)
					obj.Type = orgType
				} else {
					p.ors.Mark("numeric case not implemented")
					p.check(ors.SymOf, "OF expected")
					skipCase()
					for p.sym == ors.SymBar {
						skipCase()
					}
				}
			} else {
				p.ors.Mark("ident expected")
			}
			p.check(ors.SymEnd, "no END")
		}
		p.org.CheckRegs()
		if p.sym == ors.SymSemicolon {
			p.nextSym()
		} else if p.sym < ors.SymSemicolon {
			p.ors.Mark("missing semicolon?")
		}
		if p.sym > ors.SymSemicolon {
			break
		}
	}
}

// Types and declarations

func (p *Parser) identList(class orb.Class) (first *orb.Object) {
	if p.sym == ors.SymIdent {
		first = p.orb.NewObj(p.ors.Id, class)
		p.nextSym()
		first.Expo = p.checkExport()
		for p.sym == ors.SymComma {
			p.nextSym()
			if p.sym == ors.SymIdent {
				obj := p.orb.NewObj(p.ors.Id, class)
				p.nextSym()
				obj.Expo = p.checkExport()
			} else {
				p.ors.Mark("ident?")
			}
		}
		if p.sym == ors.SymColon {
			p.nextSym()
		} else {
			p.ors.Mark(":?")
		}
	} else {
		first = nil
	}
	return first
}

func (p *Parser) arrayType() *orb.Type {
	typ := &orb.Type{
		Form: orb.FormNoTyp,
	}
	var x org.Item
	p.expression(&x)
	var length int32
	if (x.Mode == orb.ClassConst) && (x.Type.Form == orb.FormInt) && (x.A >= 0) {
		length = x.A
	} else {
		length = 1
		p.ors.Mark("not a valid length")
	}
	if p.sym == ors.SymOf {
		p.nextSym()
		typ.Base = p._type()
		if (typ.Base.Form == orb.FormArray) && (typ.Base.Len < 0) {
			p.ors.Mark("dyn array not allowed")
		}
	} else if p.sym == ors.SymComma {
		p.nextSym()
		typ.Base = p.arrayType()
	} else {
		p.ors.Mark("missing OF")
		typ.Base = p.orb.IntType
	}
	typ.Size = (length*typ.Base.Size + 3) / 4 * 4
	typ.Form = orb.FormArray
	typ.Len = length
	return typ
}

func (p *Parser) recordType() *orb.Type {
	typ := &orb.Type{
		Form:   orb.FormNoTyp,
		Base:   nil,
		Mno:    -p.level,
		NOfPar: 0,
	}
	offset := int32(0)
	var bot *orb.Object
	if p.sym == ors.SymLparen {
		// record extension
		p.nextSym()
		if p.level != 0 {
			p.ors.Mark("extension of local types not implemented")
		}
		if p.sym == ors.SymIdent {
			base := p.qualIdent()
			if base.Class == orb.ClassTyp {
				if base.Type.Form == orb.FormRecord {
					typ.Base = base.Type
				} else {
					typ.Base = p.orb.IntType
					p.ors.Mark("invalid extension")
				}
				// "NOfPar" here abused for extension level
				typ.NOfPar = typ.Base.NOfPar + 1
				bot = typ.Base.Dsc
				offset = typ.Base.Size
			} else {
				p.ors.Mark("type expected")
			}
		} else {
			p.ors.Mark("ident expected")
		}
		p.check(ors.SymRparen, "no )")
	}
	for p.sym == ors.SymIdent {
		// fields
		n := int32(0)
		obj := bot
		for p.sym == ors.SymIdent {
			obj0 := obj
			for (obj0 != nil) && (obj0.Name != p.ors.Id) {
				obj0 = obj0.Next
			}
			if obj0 != nil {
				p.ors.Mark("mult def")
			}
			obj = &orb.Object{
				Name:  p.ors.Id,
				Class: orb.ClassFld,
				Next:  obj,
			}
			n++
			p.nextSym()
			obj.Expo = p.checkExport()
			if (p.sym != ors.SymComma) && (p.sym != ors.SymColon) {
				p.ors.Mark("comma expected")
			} else if p.sym == ors.SymComma {
				p.nextSym()
			}
		}
		p.check(ors.SymColon, "colon expected")
		tp := p._type()
		if (tp.Form == orb.FormArray) && (tp.Len < 0) {
			p.ors.Mark("dyn array not allowed")
		}
		if tp.Size > 1 {
			offset = (offset + 3) / 4 * 4
		}
		offset = offset + n*tp.Size
		off := offset
		obj0 := obj
		for obj0 != bot {
			obj0.Type = tp
			obj0.Lev = 0
			off = off - tp.Size
			obj0.Val = off
			obj0 = obj0.Next
		}
		bot = obj
		if p.sym == ors.SymSemicolon {
			p.nextSym()
		} else if p.sym != ors.SymEnd {
			p.ors.Mark(" ; or END")
		}
	}
	typ.Form = orb.FormRecord
	typ.Dsc = bot
	typ.Size = (offset + 3) / 4 * 4
	return typ
}

func (p *Parser) fpSection(adr, nOfPar *int32) {
	var cl orb.Class
	if p.sym == ors.SymVar {
		p.nextSym()
		cl = orb.ClassPar
	} else {
		cl = orb.ClassVar
	}
	first := p.identList(cl)
	tp := p.formalType(0)
	rdo := false
	if (cl == orb.ClassVar) && (tp.Form >= orb.FormArray) {
		cl = orb.ClassPar
		rdo = true
	}
	var parSize int32
	if ((tp.Form == orb.FormArray) && (tp.Len < 0)) || (tp.Form == orb.FormRecord) {
		// open array or record, needs second word for length or type tag
		parSize = 2 * org.WordSize
	} else {
		parSize = org.WordSize
	}
	obj := first
	for obj != nil {
		*nOfPar++
		obj.Class = cl
		obj.Type = tp
		obj.Rdo = rdo
		obj.Lev = p.level
		obj.Val = *adr
		*adr += parSize
		obj = obj.Next
	}
	if *adr >= 52 {
		p.ors.Mark("too many parameters")
	}
}

func (p *Parser) procedureType(pType *orb.Type, parBlkSize *int32) {
	pType.Base = p.orb.NoType
	size := *parBlkSize
	nOfPar := int32(0)
	pType.Dsc = nil
	if p.sym == ors.SymLparen {
		p.nextSym()
		if p.sym == ors.SymRparen {
			p.nextSym()
		} else {
			p.fpSection(&size, &nOfPar)
			for p.sym == ors.SymSemicolon {
				p.nextSym()
				p.fpSection(&size, &nOfPar)
			}
			p.check(ors.SymRparen, "no )")
		}
		if p.sym == ors.SymColon {
			// function
			p.nextSym()
			if p.sym == ors.SymIdent {
				obj := p.qualIdent()
				pType.Base = obj.Type
				if !((obj.Class == orb.ClassTyp) && ((obj.Type.Form >= orb.FormByte && obj.Type.Form <= orb.FormPointer) || obj.Type.Form == orb.FormProc)) {
					p.ors.Mark("illegal function type")
				}
			} else {
				p.ors.Mark("type identifier expected")
			}
		}
	}
	pType.NOfPar = nOfPar
	*parBlkSize = size
}

func (p *Parser) formalType(dim int) (typ *orb.Type) {
	if p.sym == ors.SymIdent {
		obj := p.qualIdent()
		if obj.Class == orb.ClassTyp {
			typ = obj.Type
		} else {
			p.ors.Mark("not a type")
			typ = p.orb.IntType
		}
	} else if p.sym == ors.SymArray {
		p.nextSym()
		p.check(ors.SymOf, "OF ?")
		if dim >= 1 {
			p.ors.Mark("multi-dimensional open arrays not implemented")
		}
		typ = &orb.Type{
			Form: orb.FormArray,
			Len:  -1,
			Size: 2 * org.WordSize,
		}
		typ.Base = p.formalType(dim + 1)
	} else if p.sym == ors.SymProcedure {
		p.nextSym()
		p.orb.OpenScope()
		typ = &orb.Type{
			Form: orb.FormProc,
			Size: org.WordSize,
		}
		dmy := int32(0)
		p.procedureType(typ, &dmy)
		typ.Dsc = p.orb.TopScope.Next
		p.orb.CloseScope()
	} else {
		p.ors.Mark("identifier expected")
		typ = p.orb.NoType
	}
	return typ
}

func (p *Parser) checkRecLevel(lev int32) {
	if lev != 0 {
		p.ors.Mark("ptr base must be global")
	}
}

func (p *Parser) _type() *orb.Type {
	var typ *orb.Type
	typ = p.orb.IntType // sync
	if p.sym != ors.SymIdent && p.sym < ors.SymArray {
		p.ors.Mark("not a type")
		for {
			p.nextSym()
			if p.sym == ors.SymIdent || p.sym >= ors.SymArray {
				break
			}
		}
	}
	if p.sym == ors.SymIdent {
		obj := p.qualIdent()
		if obj.Class == orb.ClassTyp {
			if (obj.Type != nil) && (obj.Type.Form != orb.FormNoTyp) {
				typ = obj.Type
			}
		} else {
			p.ors.Mark("not a type or undefined")
		}
	} else if p.sym == ors.SymArray {
		p.nextSym()
		typ = p.arrayType()
	} else if p.sym == ors.SymRecord {
		p.nextSym()
		typ = p.recordType()
		p.check(ors.SymEnd, "no END")
	} else if p.sym == ors.SymPointer {
		p.nextSym()
		p.check(ors.SymTo, "no TO")
		typ = &orb.Type{
			Form: orb.FormPointer,
			Size: org.WordSize,
			Base: p.orb.IntType,
		}
		if p.sym == ors.SymIdent {
			obj := p.orb.ThisObj()
			if obj != nil {
				if (obj.Class == orb.ClassTyp) && (obj.Type.Form == orb.FormRecord || obj.Type.Form == orb.FormNoTyp) {
					p.checkRecLevel(obj.Lev)
					typ.Base = obj.Type
				} else if obj.Class == orb.ClassMod {
					p.ors.Mark("external base type not implemented")
				} else {
					p.ors.Mark("no valid base type")
				}
			} else {
				p.checkRecLevel(p.level)
				// enter into list of forward references to be fixed in `declarations`
				p.pbsList = append(p.pbsList, &ptrBase{
					name: p.ors.Id,
					typ:  typ,
				})
			}
			p.nextSym()
		} else {
			typ.Base = p._type()
			if (typ.Base.Form != orb.FormRecord) || (typ.Base.TypObj == nil) {
				p.ors.Mark("must point to named record")
			}
			p.checkRecLevel(p.level)
		}
	} else if p.sym == ors.SymProcedure {
		p.nextSym()
		p.orb.OpenScope()
		typ = &orb.Type{
			Form: orb.FormProc,
			Size: org.WordSize,
		}
		dmy := int32(0)
		p.procedureType(typ, &dmy)
		typ.Dsc = p.orb.TopScope.Next
		p.orb.CloseScope()
	} else {
		p.ors.Mark("illegal type")
	}
	return typ
}

func (p *Parser) declarations(varSize *int32) {
	p.pbsList = nil
	if p.sym < ors.SymConst && p.sym != ors.SymEnd && p.sym != ors.SymReturn {
		p.ors.Mark("declaration?")
		for {
			p.nextSym()
			if p.sym >= ors.SymConst || p.sym == ors.SymEnd || p.sym == ors.SymReturn {
				break
			}
		}
	}
	if p.sym == ors.SymConst {
		p.nextSym()
		for p.sym == ors.SymIdent {
			id := p.ors.Id
			p.nextSym()
			expo := p.checkExport()
			if p.sym == ors.SymEql {
				p.nextSym()
			} else {
				p.ors.Mark("= ?")
			}
			var x org.Item
			p.expression(&x)
			if (x.Type.Form == orb.FormString) && (x.B == 2) {
				p.org.StrToChar(&x)
			}
			obj := p.orb.NewObj(id, orb.ClassConst)
			obj.Expo = expo
			if x.Mode == orb.ClassConst {
				obj.Val = x.A
				obj.Lev = x.B
				obj.Type = x.Type
			} else {
				p.ors.Mark("expression not constant")
				obj.Type = p.orb.IntType
			}
			p.check(ors.SymSemicolon, "; missing")
		}
	}
	if p.sym == ors.SymType {
		p.nextSym()
		for p.sym == ors.SymIdent {
			id := p.ors.Id
			p.nextSym()
			expo := p.checkExport()
			if p.sym == ors.SymEql {
				p.nextSym()
			} else {
				p.ors.Mark("=?")
			}
			tp := p._type()
			obj := p.orb.NewObj(id, orb.ClassTyp)
			obj.Type = tp
			obj.Expo = expo
			obj.Lev = p.level
			if tp.TypObj == nil {
				tp.TypObj = obj
			}
			if expo && (obj.Type.Form == orb.FormRecord) {
				obj.ExNo = byte(p.exNo)
				p.exNo++
			} else {
				obj.ExNo = 0
			}
			if tp.Form == orb.FormRecord {
				// check whether this is base of a pointer type; search and fixup
				for _, ptBase := range p.pbsList {
					if obj.Name == ptBase.name {
						ptBase.typ.Base = obj.Type
					}
				}
				if p.level == 0 {
					p.org.BuildTD(tp, &p.dc) // type descriptor; len used as its address
				}
			}
			p.check(ors.SymSemicolon, "; missing")
		}
	}
	if p.sym == ors.SymVar {
		p.nextSym()
		for p.sym == ors.SymIdent {
			first := p.identList(orb.ClassVar)
			tp := p._type()
			obj := first
			for obj != nil {
				obj.Type = tp
				obj.Lev = p.level
				if tp.Size > 1 {
					*varSize = (*varSize + 3) / 4 * 4 // align
				}
				obj.Val = *varSize
				*varSize += obj.Type.Size
				if obj.Expo {
					obj.ExNo = byte(p.exNo)
					p.exNo++
				}
				obj = obj.Next
			}
			p.check(ors.SymSemicolon, "; missing")
		}
	}
	*varSize = (*varSize + 3) / 4 * 4 // align
	for _, ptBase := range p.pbsList {
		if ptBase.typ.Base.Form == orb.FormInt {
			p.ors.Mark("undefined pointer base of")
		}
	}
	if p.sym > ors.SymConst && p.sym <= ors.SymVar {
		p.ors.Mark("declaration in bad order")
	}
}

func (p *Parser) procedureDecl() {
	interrupt := false
	p.nextSym()
	if p.sym == ors.SymTimes {
		p.nextSym()
		interrupt = true
	}
	if p.sym == ors.SymIdent {
		procId := p.ors.Id
		p.nextSym()
		proc := p.orb.NewObj(p.ors.Id, orb.ClassConst)
		var parBlkSize int32
		if interrupt {
			parBlkSize = 12
		} else {
			parBlkSize = 4
		}
		typ := &orb.Type{
			Form: orb.FormProc,
			Size: org.WordSize,
		}
		proc.Type = typ
		proc.Val = -1
		proc.Lev = p.level
		proc.Expo = p.checkExport()
		if proc.Expo {
			proc.ExNo = byte(p.exNo)
			p.exNo++
		}
		p.orb.OpenScope()
		p.level++
		typ.Base = p.orb.NoType
		p.procedureType(typ, &parBlkSize) // formal parameter list
		p.check(ors.SymSemicolon, "no ;")
		locBlkSize := parBlkSize
		p.declarations(&locBlkSize)
		proc.Val = p.org.Here() * 4
		proc.Type.Dsc = p.orb.TopScope.Next
		if p.sym == ors.SymProcedure {
			L := int32(0)
			p.org.FJump(&L)
			for {
				p.procedureDecl()
				p.check(ors.SymSemicolon, "no ;")
				if p.sym != ors.SymProcedure {
					break
				}
			}
			p.org.FixOne(L)
			proc.Val = p.org.Here() * 4
			proc.Type.Dsc = p.orb.TopScope.Next
		}
		p.org.Enter(parBlkSize, locBlkSize, interrupt)
		if p.sym == ors.SymBegin {
			p.nextSym()
			p.statSequence()
		}
		var x org.Item
		if p.sym == ors.SymReturn {
			p.nextSym()
			p.expression(&x)
			if typ.Base == p.orb.NoType {
				p.ors.Mark("this is not a function")
			} else if !p.compTypes(typ.Base, x.Type, false) {
				p.ors.Mark("wrong result type")
			}
		} else if typ.Base.Form != orb.FormNoTyp {
			p.ors.Mark("function without result")
			typ.Base = p.orb.NoType
		}
		p.org.Return(typ.Base.Form, &x, locBlkSize, interrupt)
		p.orb.CloseScope()
		p.level--
		p.check(ors.SymEnd, "no END")
		if p.sym == ors.SymIdent {
			if p.ors.Id != procId {
				p.ors.Mark("no match")
			}
			p.nextSym()
		} else {
			p.ors.Mark("no proc id")
		}
	} else {
		p.ors.Mark("proc id expected")
	}
}

func (p *Parser) importMod() {
	var impId, impId1 ors.Ident
	if p.sym == ors.SymIdent {
		impId = p.ors.Id
		p.nextSym()
		if p.sym == ors.SymBecomes {
			p.nextSym()
			if p.sym == ors.SymIdent {
				impId1 = p.ors.Id
				p.nextSym()
			} else {
				p.ors.Mark("id expected")
				impId1 = impId
			}
		} else {
			impId1 = impId
		}
		p.orb.Import(impId, impId1)
	} else {
		p.ors.Mark("id expected")
	}
}

func (p *Parser) module() {
	p.log("  compiling ")
	p.nextSym()
	if p.sym == ors.SymModule {
		p.nextSym()
		if p.sym == ors.SymTimes {
			p.version = 0
			p.dc = 8
			p.log("*")
			p.nextSym()
		} else {
			p.dc = 0
			p.version = 1
		}
		p.orb.Init()
		p.orb.OpenScope()
		if p.sym == ors.SymIdent {
			p.modId = p.ors.Id
			p.nextSym()
			p.log(p.modId)
		} else {
			p.ors.Mark("identifier expected")
		}
		p.check(ors.SymSemicolon, "no ;")
		p.level = 0
		p.exNo = 1
		if p.sym == ors.SymImport {
			p.nextSym()
			p.importMod()
			for p.sym == ors.SymComma {
				p.nextSym()
				p.importMod()
			}
			p.check(ors.SymSemicolon, "; missing")
		}
		p.org.Open(p.version)
		p.declarations(&p.dc)
		p.org.SetDataSize((p.dc + 3) / 4 * 4)
		for p.sym == ors.SymProcedure {
			p.procedureDecl()
			p.check(ors.SymSemicolon, "no ;")
		}
		p.org.Header()
		if p.sym == ors.SymBegin {
			p.nextSym()
			p.statSequence()
		}
		p.check(ors.SymEnd, "no END")
		if p.sym == ors.SymIdent {
			if p.ors.Id != p.modId {
				p.ors.Mark("no match")
			}
			p.nextSym()
		} else {
			p.ors.Mark("identifier missing")
		}
		if p.sym != ors.SymPeriod {
			p.ors.Mark("period missing")
		}
		key := int32(0)
		if p.ors.ErrCnt == 0 && p.version != 0 {
			key, p.newSF = p.orb.Export(p.modId, p.newSF)
			if p.newSF {
				p.log(" new symbol file")
			}
		}
		if p.ors.ErrCnt == 0 {
			p.org.Close(p.modId, key, p.exNo)
			p.log(fmt.Sprintf(" %d %d %X", p.org.PC, p.dc, uint32(key)))
		} else {
			p.log("\ncompilation FAILED")
		}
		p.log("\n")
		p.orb.CloseScope()
		p.pbsList = nil
	} else {
		p.ors.Mark("must start with MODULE")
	}
}

func (p *Parser) log(a ...interface{}) {
	_, _ = fmt.Fprint(p.w, a...)
}

func CompileFile(path string, newSF bool) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	return Compile(f, newSF)
}

func Compile(r io.Reader, newSF bool) (err error) {
	defer func() {
		if rec := recover(); rec != nil {
			err = rec.(error)
		}
	}()

	w := os.Stdout
	s := ors.NewScanner(r, w)
	b := orb.NewBase(s)
	g := org.NewGenerator(s, b)
	p := NewParser(s, b, g, w)
	p.newSF = newSF
	p.module()
	return nil
}
