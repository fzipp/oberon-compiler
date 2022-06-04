// N.Wirth, 16.4.2016 / 4.4.2017 / 31.5.2019  Oberon compiler; code generator for RISC
// Ported from Oberon to Go by Frederik Zipp, 2021.

// Package org contains the code generator for the Oberon RISC compiler.
package org

import (
	"bufio"
	"io"
	"math"
	"os"

	"github.com/fzipp/oberon-compiler/files"
	"github.com/fzipp/oberon-compiler/orb"
	"github.com/fzipp/oberon-compiler/ors"
)

const WordSize = 4

// for RISC-0 only
const (
	stkOrg0 = -64
	varOrg0 = 0
)

// dedicated registers
const (
	mt  = 12
	sp  = 14
	lnk = 15
)

const (
	maxCode = 8000
	maxStrx = 2400
	maxTD   = 160
	c24     = 0x1000000
)

// internal item modes
const (
	classReg  orb.Class = 10
	classRegI orb.Class = 11
	classCond orb.Class = 12
)

// frequently used opcodes
const (
	opU   = 0x2000
	opV   = 0x1000
	opMov = 0
	opLsl = 1
	opAsr = 2
	opRor = 3
	opAnd = 4
	opAnn = 5
	opIor = 6
	opXor = 7
	opAdd = 8
	opSub = 9
	opCmp = 9
	opMul = 10
	opDiv = 11
	opFad = 12
	opFsb = 13
	opFml = 14
	opFdv = 15
	opLdr = 8
	opStr = 10
	opBR  = 0
	opBLR = 1
	opBC  = 2
	opBL  = 3
	opMI  = 0
	opPL  = 8
	opEQ  = 1
	opNE  = 9
	opLT  = 5
	opGE  = 13
	opLE  = 6
	opGT  = 14
)

// Item forms and meaning of fields:
//
//	mode         r      a       b
//	--------------------------------------
//	ClassConst   -      value   (proc adr)  (immediate value)
//	ClassVar     base   off     -           (direct adr)
//	ClassPar     -      off0    off1        (indirect adr)
//	classReg     regno
//	classRegI    regno  off     -
//	classCond    cond   Fchain  Tchain
type Item struct {
	Mode orb.Class
	Type *orb.Type
	A, B int32
	r    int32
	Rdo  bool // read only
}

// Generator
// Code generator for Oberon compiler for RISC processor.
// Procedural interface to Parser ORP; result in array "code".
// Method Close writes code-files
type Generator struct {
	ors *ors.Scanner
	orb *orb.Base

	PC      int32 // program counter
	varSize int32 // data index
	tdx     int32
	strx    int32
	entry   int32 // main entry point
	rh      int32 // available registers R[0] ... R[H-1]
	frame   int32 // frame offset changed in saveRegs and restoreRegs

	// origins of lists of locations to be fixed up by loader
	fixOrgP, fixOrgD, fixOrgT int32

	check   bool  // emit run-time checks
	version int32 // 0 = RISC-0, 1 = RISC-5

	relMap [6]int32 // condition codes for relations
	code   [maxCode]int32
	data   [maxTD]int32 // type descriptors
	str    [maxStrx]byte
}

func NewGenerator(s *ors.Scanner, b *orb.Base) *Generator {
	return &Generator{
		ors: s, orb: b,
		relMap: [...]int32{1, 9, 5, 6, 14, 13},
	}
}

// instruction assemblers according to formats

func (g *Generator) put0(op, a, b, c int32) {
	// emit format-0 instruction
	g.code[g.PC] = ((a<<4+b)<<4+op)<<16 + c
	g.PC++
}

func (g *Generator) put1(op, a, b, im int32) {
	// emit format-1 instruction, -0x10000 <= im < 0x10000
	if im < 0 {
		op += opV
	}
	g.code[g.PC] = (((a+0x40)<<4+b)<<4+op)<<16 + (im & 0xFFFF)
	g.PC++
}

func (g *Generator) put1a(op, a, b, im int32) {
	// same as put1, but with range test  -0x10000 <= im < 0x10000
	if (im >= -0x10000) && (im <= 0xFFFF) {
		g.put1(op, a, b, im)
	} else {
		g.put1(opMov+opU, g.rh, 0, im>>16)
		if im&0xFFFF != 0 {
			g.put1(opIor, g.rh, g.rh, im&0xFFFF)
		}
		g.put0(op, a, b, g.rh)
	}
}

func (g *Generator) put2(op, a, b, off int32) {
	g.code[g.PC] = (((op<<4+a)<<4 + b) << 20) + (off & 0xFFFFF)
	g.PC++
}

func (g *Generator) put3(op, cond, off int32) {
	// emit branch instruction
	g.code[g.PC] = ((op+12)<<4+cond)<<24 + (off & 0xFFFFFF)
	g.PC++
}

func (g *Generator) incR() {
	if g.rh < mt-1 {
		g.rh++
	} else {
		g.ors.Mark("register stack overflow")
	}
}

func (g *Generator) CheckRegs() {
	if g.rh != 0 {
		g.ors.Mark("Reg Stack")
		g.rh = 0
	}
	if g.PC >= maxCode-40 {
		g.ors.Mark("program too long")
	}
	if g.frame != 0 {
		g.ors.Mark("frame error")
		g.frame = 0
	}
}

func (g *Generator) setCC(x *Item, n int32) {
	x.Mode = classCond
	x.A = 0
	x.B = 0
	x.r = n
}

func (g *Generator) trap(cond, num int32) {
	g.put3(opBLR, cond, int32(g.ors.Pos())*0x100+num*0x10+mt)
}

// handling of forward reference, fixups of branch addresses and constant tables

func (g *Generator) negated(cond int32) int32 {
	if cond < 8 {
		cond += 8
	} else {
		cond -= 8
	}
	return cond
}

func (g *Generator) fix(at, with int32) {
	g.code[at] = int32(uint32(g.code[at])&0xFF000000) + (with & 0xFFFFFF)
}

func (g *Generator) FixOne(at int32) {
	g.fix(at, g.PC-at-1)
}

func (g *Generator) FixLink(L int32) {
	for L != 0 {
		L1 := g.code[L] & 0x3FFFF
		g.fix(L, g.PC-L-1)
		L = L1
	}
}

func (g *Generator) fixLinkWith(L0, dst int32) {
	for L0 != 0 {
		L1 := g.code[L0] & 0xFFFFFF
		g.code[L0] = int32(uint32(g.code[L0])&0xFF000000) + ((dst - L0 - 1) & 0xFFFFFF)
		L0 = L1
	}
}

func (g *Generator) merged(L0, L1 int32) int32 {
	if L0 != 0 {
		var L2 int32
		L3 := L0
		for {
			L2 = L3
			L3 = g.code[L2] & 0x3FFFF
			if L3 == 0 {
				break
			}
		}
		g.code[L2] = g.code[L2] + L1
		L1 = L0
	}
	return L1
}

// loading of operands and addresses into registers

func (g *Generator) getSB(base int32) {
	if g.version == 0 {
		g.put1(opMov, g.rh, 0, varOrg0)
	} else {
		g.put2(opLdr, g.rh, -base, g.PC-g.fixOrgD)
		g.fixOrgD = g.PC - 1
	}
}

func (g *Generator) nilCheck() {
	if g.check {
		g.trap(opEQ, 4)
	}
}

func (g *Generator) load(x *Item) {
	var op int32
	if x.Type.Size == 1 {
		op = opLdr + 1
	} else {
		op = opLdr
	}
	if x.Mode != classReg {
		if x.Mode == orb.ClassConst {
			if x.Type.Form == orb.FormProc {
				if x.r > 0 {
					g.ors.Mark("not allowed")
				} else if x.r == 0 {
					g.put3(opBL, 7, 0)
					g.put1a(opSub, g.rh, lnk, g.PC*4-x.A)
				} else {
					g.getSB(x.r)
					g.put1(opAdd, g.rh, g.rh, x.A+0x100) // mark as progbase-relative
				}
			} else if (x.A <= 0xFFFF) && (x.A >= -0x10000) {
				g.put1(opMov, g.rh, 0, x.A)
			} else {
				g.put1(opMov+opU, g.rh, 0, (x.A>>16)&0xFFFF)
				if x.A%0x10000 != 0 {
					g.put1(opIor, g.rh, g.rh, x.A&0xFFFF)
				}
			}
			x.r = g.rh
			g.incR()
		} else if x.Mode == orb.ClassVar {
			if x.r > 0 {
				// local
				g.put2(op, g.rh, sp, x.A+g.frame)
			} else {
				g.getSB(x.r)
				g.put2(op, g.rh, g.rh, x.A)
			}
			x.r = g.rh
			g.incR()
		} else if x.Mode == orb.ClassPar {
			g.put2(opLdr, g.rh, sp, x.A+g.frame)
			g.put2(op, g.rh, g.rh, x.B)
			x.r = g.rh
			g.incR()
		} else if x.Mode == classRegI {
			g.put2(op, x.r, x.r, x.A)
		} else if x.Mode == classCond {
			g.put3(opBC, g.negated(x.r), 2)
			g.FixLink(x.B)
			g.put1(opMov, g.rh, 0, 1)
			g.put3(opBC, 7, 1)
			g.FixLink(x.A)
			g.put1(opMov, g.rh, 0, 0)
			x.r = g.rh
			g.incR()
		}
		x.Mode = classReg
	}
}

func (g *Generator) loadAdr(x *Item) {
	if x.Mode == orb.ClassVar {
		if x.r > 0 {
			// local
			g.put1a(opAdd, g.rh, sp, x.A+g.frame)
		} else {
			g.getSB(x.r)
			g.put1a(opAdd, g.rh, g.rh, x.A)
		}
		x.r = g.rh
		g.incR()
	} else if x.Mode == orb.ClassPar {
		g.put2(opLdr, g.rh, sp, x.A+g.frame)
		if x.B != 0 {
			g.put1a(opAdd, g.rh, g.rh, x.B)
		}
		x.r = g.rh
		g.incR()
	} else if x.Mode == classRegI {
		if x.A != 0 {
			g.put1a(opAdd, x.r, x.r, x.A)
		}
	} else {
		g.ors.Mark("address error")
	}
	x.Mode = classReg
}

func (g *Generator) loadCond(x *Item) {
	if x.Type.Form == orb.FormBool {
		if x.Mode == orb.ClassConst {
			x.r = 15 - x.A*8
		} else {
			g.load(x)
			if g.code[g.PC-1]>>30 != -2 {
				g.put1(opCmp, x.r, x.r, 0)
			}
			x.r = opNE
			g.rh--
		}
		x.Mode = classCond
		x.A = 0
		x.B = 0
	} else {
		g.ors.Mark("not Boolean?")
	}
}

func (g *Generator) loadTypTagAdr(t *orb.Type) {
	var x Item
	x.Mode = orb.ClassVar
	x.A = t.Len
	x.r = -t.Mno
	g.loadAdr(&x)
}

func (g *Generator) loadStringAdr(x *Item) {
	g.getSB(0)
	g.put1a(opAdd, g.rh, g.rh, g.varSize+x.A)
	x.Mode = classReg
	x.r = g.rh
	g.incR()
}

// Items: Conversion from constants or from Objects on the Heap to Items on the Stack

func (g *Generator) MakeConstItem(x *Item, typ *orb.Type, val int32) {
	x.Mode = orb.ClassConst
	x.Type = typ
	x.A = val
}

func (g *Generator) MakeRealItem(x *Item, val float32) {
	x.Mode = orb.ClassConst
	x.Type = g.orb.RealType
	x.A = int32(math.Float32bits(val))
}

func (g *Generator) MakeStringItem(x *Item, length int32) {
	// copies string from ORS-buffer to ORG-string array
	x.Mode = orb.ClassConst
	x.Type = g.orb.StrType
	x.A = g.strx
	x.B = length
	if g.strx+length+4 < maxStrx {
		i := 0
		for length > 0 {
			g.str[g.strx] = g.ors.Str[i]
			g.strx++
			i++
			length--
		}
		for g.strx%4 != 0 {
			g.str[g.strx] = 0
			g.strx++
		}
	} else {
		g.ors.Mark("too many strings")
	}
}

func (g *Generator) MakeItem(x *Item, y *orb.Object, curLev int32) {
	x.Mode = y.Class
	x.Type = y.Type
	x.A = y.Val
	x.Rdo = y.Rdo
	if y.Class == orb.ClassPar {
		x.B = 0
	} else if y.Class == orb.ClassConst && y.Type.Form == orb.FormString {
		x.B = y.Lev // len
	} else {
		x.r = y.Lev
	}
	if (y.Lev > 0) && (y.Lev != curLev) && (y.Class != orb.ClassConst) {
		g.ors.Mark("not accessible")
	}
}

// Code generation for Selectors, Variables, Constants

func (g *Generator) Field(x *Item, y *orb.Object) {
	if x.Mode == orb.ClassVar {
		if x.r >= 0 {
			x.A = x.A + y.Val
		} else {
			g.loadAdr(x)
			x.Mode = classRegI
			x.A = y.Val
		}
	} else if x.Mode == classRegI {
		x.A = x.A + y.Val
	} else if x.Mode == orb.ClassPar {
		x.B = x.B + y.Val
	}
}

func (g *Generator) Index(x, y *Item) {
	s := x.Type.Base.Size
	lim := x.Type.Len
	if (y.Mode == orb.ClassConst) && (lim >= 0) {
		if (y.A < 0) || (y.A >= lim) {
			g.ors.Mark("bad index")
		}
		if x.Mode == orb.ClassVar || x.Mode == classRegI {
			x.A = y.A*s + x.A
		} else if x.Mode == orb.ClassPar {
			x.B = y.A*s + x.B
		}
	} else {
		g.load(y)
		if g.check {
			// check array bounds
			if lim >= 0 {
				g.put1a(opCmp, g.rh, y.r, lim)
			} else {
				// open array
				if x.Mode == orb.ClassVar || x.Mode == orb.ClassPar {
					g.put2(opLdr, g.rh, sp, x.A+4+g.frame)
					g.put0(opCmp, g.rh, y.r, g.rh)
				} else {
					g.ors.Mark("error in Index")
				}
			}
			g.trap(10, 1) // BCC
		}
		if s == 4 {
			g.put1(opLsl, y.r, y.r, 2)
		} else if s > 1 {
			g.put1a(opMul, y.r, y.r, s)
		}
		if x.Mode == orb.ClassVar {
			if x.r > 0 {
				g.put0(opAdd, y.r, sp, y.r)
				x.A += g.frame
			} else {
				g.getSB(x.r)
				if x.r == 0 {
					g.put0(opAdd, y.r, g.rh, y.r)
				} else {
					g.put1a(opAdd, g.rh, g.rh, x.A)
					g.put0(opAdd, y.r, g.rh, y.r)
					x.A = 0
				}
			}
			x.r = y.r
			x.Mode = classRegI
		} else if x.Mode == orb.ClassPar {
			g.put2(opLdr, g.rh, sp, x.A+g.frame)
			g.put0(opAdd, y.r, g.rh, y.r)
			x.Mode = classRegI
			x.r = y.r
			x.A = x.B
		} else if x.Mode == classRegI {
			g.put0(opAdd, x.r, x.r, y.r)
			g.rh--
		}
	}
}

func (g *Generator) DeRef(x *Item) {
	if x.Mode == orb.ClassVar {
		if x.r > 0 {
			// local
			g.put2(opLdr, g.rh, sp, x.A+g.frame)
		} else {
			g.getSB(x.r)
			g.put2(opLdr, g.rh, g.rh, x.A)
		}
		g.nilCheck()
		x.r = g.rh
		g.incR()
	} else if x.Mode == orb.ClassPar {
		g.put2(opLdr, g.rh, sp, x.A+g.frame)
		g.put2(opLdr, g.rh, g.rh, x.B)
		g.nilCheck()
		x.r = g.rh
		g.incR()
	} else if x.Mode == classRegI {
		g.put2(opLdr, x.r, x.r, x.A)
		g.nilCheck()
	} else if x.Mode != classReg {
		g.ors.Mark("bad mode in DeRef")
	}
	x.Mode = classRegI
	x.A = 0
	x.B = 0
}

func (g *Generator) q(t *orb.Type, dcw *int32) {
	// one entry of type descriptor extension table
	if t.Base != nil {
		g.q(t.Base, dcw)
		g.data[*dcw] = (t.Mno*0x1000+t.Len)*0x1000 + *dcw - g.fixOrgT
		g.fixOrgT = *dcw
		*dcw++
	}
}

func (g *Generator) findPtrFlds(typ *orb.Type, off int32, dcw *int32) {
	if typ.Form == orb.FormPointer || typ.Form == orb.FormNilTyp {
		g.data[*dcw] = off
		*dcw++
	} else if typ.Form == orb.FormRecord {
		fld := typ.Dsc
		for fld != nil {
			g.findPtrFlds(fld.Type, fld.Val+off, dcw)
			fld = fld.Next
		}
	} else if typ.Form == orb.FormArray {
		s := typ.Base.Size
		for i := int32(0); i < typ.Len; i++ {
			g.findPtrFlds(typ.Base, i*s+off, dcw)
		}
	}
}

func (g *Generator) BuildTD(t *orb.Type, dc *int32) {
	// dcw = word address
	dcw := *dc / 4
	s := t.Size // convert size for heap allocation
	if s <= 24 {
		s = 32
	} else if s <= 56 {
		s = 64
	} else if s <= 120 {
		s = 128
	} else {
		s = (s + 263) / 256 * 256
	}
	t.Len = *dc // len used as address
	g.data[dcw] = s
	dcw++
	k := t.NOfPar // extension level!
	if k > 3 {
		g.ors.Mark("ext level too large")
	} else {
		g.q(t, &dcw)
		for k < 3 {
			g.data[dcw] = -1
			dcw++
			k++
		}
	}
	g.findPtrFlds(t, 0, &dcw)
	g.data[dcw] = -1
	dcw++
	g.tdx = dcw
	*dc = dcw * 4
	if g.tdx >= maxTD {
		g.ors.Mark("too many record types")
		g.tdx = 0
	}
}

func (g *Generator) TypeTest(x *Item, t *orb.Type, varPar, isGuard bool) {
	if t == nil {
		if x.Mode >= classReg {
			g.rh--
		}
		g.setCC(x, 7)
	} else {
		var pc0 int32
		// fetch tag into RH
		if varPar {
			g.put2(opLdr, g.rh, sp, x.A+4+g.frame)
		} else {
			g.load(x)
			pc0 = g.PC
			g.put3(opBC, opEQ, 0) // NIL belongs to every pointer type
			g.put2(opLdr, g.rh, x.r, -8)
		}
		g.put2(opLdr, g.rh, g.rh, t.NOfPar*4)
		g.incR()
		g.loadTypTagAdr(t) // tag of T
		g.put0(opCmp, g.rh-1, g.rh-1, g.rh-2)
		g.rh -= 2
		if !varPar {
			g.fix(pc0, g.PC-pc0-1)
		}
		if isGuard {
			if g.check {
				g.trap(opNE, 2)
			}
		} else {
			g.setCC(x, opEQ)
			if !varPar {
				g.rh--
			}
		}
	}
}

// Code generation for Boolean operators

func (g *Generator) Not(x *Item) {
	// x := ~x
	if x.Mode != classCond {
		g.loadCond(x)
	}
	x.r = g.negated(x.r)
	x.A, x.B = x.B, x.A
}

func (g *Generator) And1(x *Item) {
	// x := x &
	if x.Mode != classCond {
		g.loadCond(x)
	}
	g.put3(opBC, g.negated(x.r), x.A)
	x.A = g.PC - 1
	g.FixLink(x.B)
	x.B = 0
}

func (g *Generator) And2(x, y *Item) {
	if y.Mode != classCond {
		g.loadCond(y)
	}
	x.A = g.merged(y.A, x.A)
	x.B = y.B
	x.r = y.r
}

func (g *Generator) Or1(x *Item) {
	// x := x OR
	if x.Mode != classCond {
		g.loadCond(x)
	}
	g.put3(opBC, x.r, x.B)
	x.B = g.PC - 1
	g.FixLink(x.A)
	x.A = 0
}

func (g *Generator) Or2(x, y *Item) {
	if y.Mode != classCond {
		g.loadCond(y)
	}
	x.A = y.A
	x.B = g.merged(y.B, x.B)
	x.r = y.r
}

// Code generation for arithmetic operators

func (g *Generator) Neg(x *Item) {
	// x := -x
	if x.Type.Form == orb.FormInt {
		if x.Mode == orb.ClassConst {
			x.A = -x.A
		} else {
			g.load(x)
			g.put1(opMov, g.rh, 0, 0)
			g.put0(opSub, x.r, g.rh, x.r)
		}
	} else if x.Type.Form == orb.FormReal {
		if x.Mode == orb.ClassConst {
			i := 0x7FFFFFFF + 1
			x.A += int32(i)
		} else {
			g.load(x)
			g.put1(opMov, g.rh, 0, 0)
			g.put0(opFsb, x.r, g.rh, x.r)
		}
	} else {
		// Form = FormSet
		if x.Mode == orb.ClassConst {
			x.A = -x.A - 1
		} else {
			g.load(x)
			g.put1(opXor, x.r, x.r, -1)
		}
	}
}

func (g *Generator) AddOp(op ors.Sym, x, y *Item) {
	// x := x +- y
	if op == ors.SymPlus {
		if x.Mode == orb.ClassConst && y.Mode == orb.ClassConst {
			x.A += y.A
		} else if y.Mode == orb.ClassConst {
			g.load(x)
			if y.A != 0 {
				g.put1a(opAdd, x.r, x.r, y.A)
			}
		} else {
			g.load(x)
			g.load(y)
			g.put0(opAdd, g.rh-2, x.r, y.r)
			g.rh--
			x.r = g.rh - 1
		}
	} else { // op == SymMinus
		if x.Mode == orb.ClassConst && y.Mode == orb.ClassConst {
			x.A -= y.A
		} else if y.Mode == orb.ClassConst {
			g.load(x)
			if y.A != 0 {
				g.put1a(opSub, x.r, x.r, y.A)
			}
		} else {
			g.load(x)
			g.load(y)
			g.put0(opSub, g.rh-2, x.r, y.r)
			g.rh--
			x.r = g.rh - 1
		}
	}
}

func (g *Generator) MulOp(x, y *Item) {
	// x := x * y
	var e int32
	if (x.Mode == orb.ClassConst) && (y.Mode == orb.ClassConst) {
		x.A *= y.A
	} else if (y.Mode == orb.ClassConst) && (y.A >= 2) && (log2(y.A, &e) == 1) {
		g.load(x)
		g.put1(opLsl, x.r, x.r, e)
	} else if y.Mode == orb.ClassConst {
		g.load(x)
		g.put1a(opMul, x.r, x.r, y.A)
	} else if (x.Mode == orb.ClassConst) && (x.A >= 2) && (log2(x.A, &e) == 1) {
		g.load(y)
		g.put1(opLsl, y.r, y.r, e)
		x.Mode = classReg
		x.r = y.r
	} else if x.Mode == orb.ClassConst {
		g.load(y)
		g.put1a(opMul, y.r, y.r, x.A)
		x.Mode = classReg
		x.r = y.r
	} else {
		g.load(x)
		g.load(y)
		g.put0(opMul, g.rh-2, x.r, y.r)
		g.rh--
		x.r = g.rh - 1
	}
}

func (g *Generator) DivOp(op ors.Sym, x, y *Item) {
	// x := x op y
	var e int32
	if op == ors.SymDiv {
		if (x.Mode == orb.ClassConst) && (y.Mode == orb.ClassConst) {
			if y.A > 0 {
				x.A /= y.A
			} else {
				g.ors.Mark("bad divisor")
			}
		} else if (y.Mode == orb.ClassConst) && (y.A >= 2) && (log2(y.A, &e) == 1) {
			g.load(x)
			g.put1(opAsr, x.r, x.r, e)
		} else if y.Mode == orb.ClassConst {
			if y.A > 0 {
				g.load(x)
				g.put1a(opDiv, x.r, x.r, y.A)
			} else {
				g.ors.Mark("bad divisor")
			}
		} else {
			g.load(y)
			if g.check {
				g.trap(opLE, 6)
			}
			g.load(x)
			g.put0(opDiv, g.rh-2, x.r, y.r)
			g.rh--
			x.r = g.rh - 1
		}
	} else {
		// op == SymMod
		if (x.Mode == orb.ClassConst) && (y.Mode == orb.ClassConst) {
			if y.A > 0 {
				x.A = x.A % y.A
			} else {
				g.ors.Mark("bad modulus")
			}
		} else if (y.Mode == orb.ClassConst) && (y.A >= 2) && (log2(y.A, &e) == 1) {
			g.load(x)
			if e <= 16 {
				g.put1(opAnd, x.r, x.r, y.A-1)
			} else {
				g.put1(opLsl, x.r, x.r, 32-e)
				g.put1(opRor, x.r, x.r, 32-e)
			}
		} else if y.Mode == orb.ClassConst {
			if y.A > 0 {
				g.load(x)
				g.put1a(opDiv, x.r, x.r, y.A)
				g.put0(opMov+opU, x.r, 0, 0)
			} else {
				g.ors.Mark("bad modulus")
			}
		} else {
			g.load(y)
			if g.check {
				g.trap(opLE, 6)
			}
			g.load(x)
			g.put0(opDiv, g.rh-2, x.r, y.r)
			g.put0(opMov+opU, g.rh-2, 0, 0)
			g.rh--
			x.r = g.rh - 1
		}
	}
}

// Code generation for REAL operators

func (g *Generator) RealOp(op ors.Sym, x, y *Item) {
	// x := x op y
	g.load(x)
	g.load(y)
	if op == ors.SymPlus {
		g.put0(opFad, g.rh-2, x.r, y.r)
	} else if op == ors.SymMinus {
		g.put0(opFsb, g.rh-2, x.r, y.r)
	} else if op == ors.SymTimes {
		g.put0(opFml, g.rh-2, x.r, y.r)
	} else if op == ors.SymRdiv {
		g.put0(opFdv, g.rh-2, x.r, y.r)
	}
	g.rh--
	x.r = g.rh - 1
}

// Code generation for set operators

func (g *Generator) Singleton(x *Item) {
	// x := {x}
	if x.Mode == orb.ClassConst {
		x.A = 1 << x.A
	} else {
		g.load(x)
		g.put1(opMov, g.rh, 0, 1)
		g.put0(opLsl, x.r, g.rh, x.r)
	}
}

func (g *Generator) Set(x, y *Item) {
	// x := {x .. y}
	if (x.Mode == orb.ClassConst) && (y.Mode == orb.ClassConst) {
		if x.A <= y.A {
			x.A = (2 << y.A) - (1 << x.A)
		} else {
			x.A = 0
		}
	} else {
		if (x.Mode == orb.ClassConst) && (x.A <= 16) {
			x.A = -1 << x.A
		} else {
			g.load(x)
			g.put1(opMov, g.rh, 0, -1)
			g.put0(opLsl, x.r, g.rh, x.r)
		}
		if (y.Mode == orb.ClassConst) && (y.A < 16) {
			g.put1(opMov, g.rh, 0, -2<<y.A)
			y.Mode = classReg
			y.r = g.rh
			g.incR()
		} else {
			g.load(y)
			g.put1(opMov, g.rh, 0, -2)
			g.put0(opLsl, y.r, g.rh, y.r)
		}
		if x.Mode == orb.ClassConst {
			if x.A != 0 {
				g.put1(opXor, y.r, y.r, -1)
				g.put1a(opAnd, g.rh-1, y.r, x.A)
			}
			x.Mode = classReg
			x.r = g.rh - 1
		} else {
			g.rh--
			g.put0(opAnn, g.rh-1, x.r, y.r)
		}
	}
}

func (g *Generator) In(x, y *Item) {
	// x := x IN y
	g.load(y)
	if x.Mode == orb.ClassConst {
		g.put1(opRor, y.r, y.r, (x.A+1)%0x20)
		g.rh--
	} else {
		g.load(x)
		g.put1(opAdd, x.r, x.r, 1)
		g.put0(opRor, y.r, y.r, x.r)
		g.rh -= 2
	}
	g.setCC(x, opMI)
}

func (g *Generator) SetOp(op ors.Sym, x, y *Item) {
	// x := x op y
	// x.Type.Form == FormSet
	if (x.Mode == orb.ClassConst) && (y.Mode == orb.ClassConst) {
		xSet := x.A
		ySet := y.A
		if op == ors.SymPlus {
			xSet = xSet | ySet
		} else if op == ors.SymMinus {
			xSet = xSet &^ ySet
		} else if op == ors.SymTimes {
			xSet = xSet & ySet
		} else if op == ors.SymRdiv {
			xSet = xSet ^ ySet
		}
		x.A = xSet
	} else if y.Mode == orb.ClassConst {
		g.load(x)
		if op == ors.SymPlus {
			g.put1a(opIor, x.r, x.r, y.A)
		} else if op == ors.SymMinus {
			g.put1a(opAnn, x.r, x.r, y.A)
		} else if op == ors.SymTimes {
			g.put1a(opAnd, x.r, x.r, y.A)
		} else if op == ors.SymRdiv {
			g.put1a(opXor, x.r, x.r, y.A)
		}
	} else {
		g.load(x)
		g.load(y)
		if op == ors.SymPlus {
			g.put0(opIor, g.rh-2, x.r, y.r)
		} else if op == ors.SymMinus {
			g.put0(opAnn, g.rh-2, x.r, y.r)
		} else if op == ors.SymTimes {
			g.put0(opAnd, g.rh-2, x.r, y.r)
		} else if op == ors.SymRdiv {
			g.put0(opXor, g.rh-2, x.r, y.r)
		}
		g.rh--
		x.r = g.rh - 1
	}
}

// Code generation for relations

func (g *Generator) IntRelation(op ors.Sym, x, y *Item) {
	// x := x < y
	if y.Mode == orb.ClassConst && y.Type.Form != orb.FormProc {
		g.load(x)
		if (y.A != 0) || !(op == ors.SymEql || op == ors.SymNeq) || (g.code[g.PC-1]>>30 != -2) {
			g.put1a(opCmp, x.r, x.r, y.A)
		}
		g.rh--
	} else {
		if x.Mode == classCond || y.Mode == classCond {
			g.ors.Mark("not implemented")
		}
		g.load(x)
		g.load(y)
		g.put0(opCmp, x.r, x.r, y.r)
		g.rh -= 2
	}
	g.setCC(x, g.relMap[op-ors.SymEql])
}

func (g *Generator) RealRelation(op ors.Sym, x, y *Item) {
	// x := x < y
	g.load(x)
	if y.Mode == orb.ClassConst && y.A == 0 {
		g.rh--
	} else {
		g.load(y)
		g.put0(opFsb, x.r, x.r, y.r)
		g.rh -= 2
	}
	g.setCC(x, g.relMap[op-ors.SymEql])
}

func (g *Generator) StringRelation(op ors.Sym, x, y *Item) {
	// x := x < y
	if x.Type.Form == orb.FormString {
		g.loadStringAdr(x)
	} else {
		g.loadAdr(x)
	}
	if y.Type.Form == orb.FormString {
		g.loadStringAdr(y)
	} else {
		g.loadAdr(y)
	}
	g.put2(opLdr+1, g.rh, x.r, 0)
	g.put1(opAdd, x.r, x.r, 1)
	g.put2(opLdr+1, g.rh+1, y.r, 0)
	g.put1(opAdd, y.r, y.r, 1)
	g.put0(opCmp, g.rh+2, g.rh, g.rh+1)
	g.put3(opBC, opNE, 2)
	g.put1(opCmp, g.rh+2, g.rh, 0)
	g.put3(opBC, opNE, -8)
	g.rh -= 2
	g.setCC(x, g.relMap[op-ors.SymEql])
}

// Code generation of Assignments

func (g *Generator) StrToChar(x *Item) {
	x.Type = g.orb.CharType
	g.strx -= 4
	x.A = int32(g.str[x.A])
}

func (g *Generator) Store(x, y *Item) {
	// x := y
	g.load(y)
	var op int32
	if x.Type.Size == 1 {
		op = opStr + 1
	} else {
		op = opStr
	}
	if x.Mode == orb.ClassVar {
		if x.r > 0 {
			// local
			g.put2(op, y.r, sp, x.A+g.frame)
		} else {
			g.getSB(x.r)
			g.put2(op, y.r, g.rh, x.A)
		}
	} else if x.Mode == orb.ClassPar {
		g.put2(opLdr, g.rh, sp, x.A+g.frame)
		g.put2(op, y.r, g.rh, x.B)
	} else if x.Mode == classRegI {
		g.put2(op, y.r, x.r, x.A)
		g.rh--
	} else {
		g.ors.Mark("bad mode in Store")
	}
	g.rh--
}

func (g *Generator) StoreStruct(x, y *Item) {
	if y.Type.Size != 0 {
		g.loadAdr(x)
		g.loadAdr(y)
		if (x.Type.Form == orb.FormArray) && (x.Type.Len > 0) {
			if y.Type.Len >= 0 {
				if x.Type.Size == y.Type.Size {
					g.put1a(opMov, g.rh, 0, (y.Type.Size+3)/4)
				} else {
					g.ors.Mark("different length/size, not implemented")
				}
			} else {
				// y  open array
				g.put2(opLdr, g.rh, sp, y.A+4)
				s := y.Type.Base.Size // element size
				pc0 := g.PC
				g.put3(opBC, opEQ, 0)
				if s == 1 {
					g.put1(opAdd, g.rh, g.rh, 3)
					g.put1(opAsr, g.rh, g.rh, 2)
				} else if s != 4 {
					g.put1a(opMul, g.rh, g.rh, s/4)
				}
				if g.check {
					g.put1a(opMov, g.rh+1, 0, (x.Type.Size+3)/4)
					g.put0(opCmp, g.rh+1, g.rh, g.rh+1)
					g.trap(opGT, 3)
				}
				g.fix(pc0, g.PC+5-pc0)
			}
		} else if x.Type.Form == orb.FormRecord {
			g.put1a(opMov, g.rh, 0, x.Type.Size/4)
		} else {
			g.ors.Mark("inadmissible assignment")
		}
		g.put2(opLdr, g.rh+1, y.r, 0)
		g.put1(opAdd, y.r, y.r, 4)
		g.put2(opStr, g.rh+1, x.r, 0)
		g.put1(opAdd, x.r, x.r, 4)
		g.put1(opSub, g.rh, g.rh, 1)
		g.put3(opBC, opNE, -6)
	}
	g.rh = 0
}

func (g *Generator) CopyString(x, y *Item) {
	// x := y
	g.loadAdr(x)
	length := x.Type.Len
	if length >= 0 {
		if length < y.B {
			g.ors.Mark("string too long")
		}
	} else if g.check {
		// open array len, frame = 0
		g.put2(opLdr, g.rh, sp, x.A+4)
		g.put1(opCmp, g.rh, g.rh, y.B)
		g.trap(opLT, 3)
	}
	g.loadStringAdr(y)
	g.put2(opLdr, g.rh, y.r, 0)
	g.put1(opAdd, y.r, y.r, 4)
	g.put2(opStr, g.rh, x.r, 0)
	g.put1(opAdd, x.r, x.r, 4)
	g.put1(opAsr, g.rh, g.rh, 24)
	g.put3(opBC, opNE, -6)
	g.rh = 0
}

// Code generation for parameters

func (g *Generator) OpenArrayParam(x *Item) {
	g.loadAdr(x)
	if x.Type.Len >= 0 {
		g.put1a(opMov, g.rh, 0, x.Type.Len)
	} else {
		g.put2(opLdr, g.rh, sp, x.A+4+g.frame)
	}
	g.incR()
}

func (g *Generator) VarParam(x *Item, fType *orb.Type) {
	xmd := x.Mode
	g.loadAdr(x)
	if (fType.Form == orb.FormArray) && (fType.Len < 0) {
		// open array
		if x.Type.Len >= 0 {
			g.put1a(opMov, g.rh, 0, x.Type.Len)
		} else {
			g.put2(opLdr, g.rh, sp, x.A+4+g.frame)
		}
		g.incR()
	} else if fType.Form == orb.FormRecord {
		if xmd == orb.ClassPar {
			g.put2(opLdr, g.rh, sp, x.A+4+g.frame)
			g.incR()
		} else {
			g.loadTypTagAdr(x.Type)
		}
	}
}

func (g *Generator) ValueParam(x *Item) {
	g.load(x)
}

func (g *Generator) StringParam(x *Item) {
	g.loadStringAdr(x)
	g.put1(opMov, g.rh, 0, x.B)
	g.incR() // len
}

// For Statements

func (g *Generator) For0(x, y *Item) {
	g.load(y)
}

func (g *Generator) For1(x, y, z, w *Item) (L int32) {
	if z.Mode == orb.ClassConst {
		g.put1a(opCmp, g.rh, y.r, z.A)
	} else {
		g.load(z)
		g.put0(opCmp, g.rh-1, y.r, z.r)
		g.rh--
	}
	L = g.PC
	if w.A > 0 {
		g.put3(opBC, opGT, 0)
	} else if w.A < 0 {
		g.put3(opBC, opLT, 0)
	} else {
		g.ors.Mark("zero increment")
		g.put3(opBC, opMI, 0)
	}
	g.Store(x, y)
	return L
}

func (g *Generator) For2(x, y, w *Item) {
	g.load(x)
	g.rh--
	g.put1a(opAdd, x.r, x.r, w.A)
}

// Branches, procedure calls, procedure prolog and epilog

func (g *Generator) Here() int32 {
	return g.PC
}

func (g *Generator) FJump(L *int32) {
	g.put3(opBC, 7, *L)
	*L = g.PC - 1
}

func (g *Generator) CFJump(x *Item) {
	if x.Mode != classCond {
		g.loadCond(x)
	}
	g.put3(opBC, g.negated(x.r), x.A)
	g.FixLink(x.B)
	x.A = g.PC - 1
}

func (g *Generator) BJump(L int32) {
	g.put3(opBC, 7, L-g.PC-1)
}

func (g *Generator) CBJump(x *Item, L int32) {
	if x.Mode != classCond {
		g.loadCond(x)
	}
	g.put3(opBC, g.negated(x.r), L-g.PC-1)
	g.FixLink(x.B)
	g.fixLinkWith(x.A, L)
}

func (g *Generator) Fixup(x *Item) {
	g.FixLink(x.A)
}

func (g *Generator) saveRegs(r int32) {
	// R[0 .. r-1]
	// r > 0
	r0 := int32(0)
	g.put1(opSub, sp, sp, r*4)
	g.frame += 4 * r
	for {
		g.put2(opStr, r0, sp, (r-r0-1)*4)
		r0++
		if r0 == r {
			break
		}
	}
}

func (g *Generator) restoreRegs(r int32) {
	// R[0 .. r-1]
	// r > 0
	r0 := r
	for {
		r0--
		g.put2(opLdr, r0, sp, (r-r0-1)*4)
		if r0 == 0 {
			break
		}
	}
	g.put1(opAdd, sp, sp, r*4)
	g.frame -= 4 * r
}

func (g *Generator) PrepCall(x *Item) (r int32) {
	// x.Type.Form == FormProc
	if x.Mode > orb.ClassPar {
		g.load(x)
	}
	r = g.rh
	if g.rh > 0 {
		g.saveRegs(g.rh)
		g.rh = 0
	}
	return r
}

func (g *Generator) Call(x *Item, r int32) {
	// x.Type.Form == FormProc
	if x.Mode == orb.ClassConst {
		if x.r >= 0 {
			g.put3(opBL, 7, (x.A/4)-g.PC-1)
		} else {
			// imported
			if g.PC-g.fixOrgP < 0x1000 {
				g.put3(opBL, 7, ((-x.r)*0x100+x.A)*0x1000+g.PC-g.fixOrgP)
				g.fixOrgP = g.PC - 1
			} else {
				g.ors.Mark("fixup impossible")
			}
		}
	} else {
		if x.Mode <= orb.ClassPar {
			g.load(x)
			g.rh--
		} else {
			g.put2(opLdr, g.rh, sp, 0)
			g.put1(opAdd, sp, sp, 4)
			r--
			g.frame -= 4
		}
		if g.check {
			g.trap(opEQ, 5)
		}
		g.put3(opBLR, 7, g.rh)
	}
	if x.Type.Base.Form == orb.FormNoTyp {
		// procedure
		g.rh = 0
	} else {
		// function
		if r > 0 {
			g.put0(opMov, r, 0, 0)
			g.restoreRegs(r)
		}
		x.Mode = classReg
		x.r = r
		g.rh = r + 1
	}
}

func (g *Generator) Enter(parBlkSize, locBlkSize int32, interrupt bool) {
	if !interrupt {
		// procedure prolog
		if locBlkSize >= 0x10000 {
			g.ors.Mark("too many locals")
		}
		a := int32(4)
		r := int32(0)
		g.put1(opSub, sp, sp, locBlkSize)
		g.put2(opStr, lnk, sp, 0)
		for a < parBlkSize {
			g.put2(opStr, r, sp, a)
			r++
			a += 4
		}
	} else {
		g.put1(opSub, sp, sp, locBlkSize)
		g.put2(opStr, 0, sp, 0)
		g.put2(opStr, 1, sp, 4)
		g.put2(opStr, 2, sp, 8)
		// R0, R1, R2 saved on stack
	}
}

func (g *Generator) Return(form orb.Form, x *Item, size int32, interrupt bool) {
	if form != orb.FormNoTyp {
		g.load(x)
	}
	if !interrupt {
		// procedure epilog
		g.put2(opLdr, lnk, sp, 0)
		g.put1(opAdd, sp, sp, size)
		g.put3(opBR, 7, lnk)
	} else {
		// interrupt return, restore R2, R1, R0
		g.put2(opLdr, 2, sp, 8)
		g.put2(opLdr, 1, sp, 4)
		g.put2(opLdr, 0, sp, 0)
		g.put1(opAdd, sp, sp, size)
		g.put3(opBR, 7, 0x10) // RTI
	}
	g.rh = 0
}

// In-line code procedures

func (g *Generator) Increment(upOrDown int32, x, y *Item) {
	var op int32
	if upOrDown == 0 {
		op = opAdd
	} else {
		op = opSub
	}
	var v int32
	if x.Type == g.orb.ByteType {
		v = 1
	} else {
		v = 0
	}
	if y.Type.Form == orb.FormNoTyp {
		y.Mode = orb.ClassConst
		y.A = 1
	}
	if (x.Mode == orb.ClassVar) && (x.r > 0) {
		zr := g.rh
		g.put2(opLdr+v, zr, sp, x.A)
		g.incR()
		if y.Mode == orb.ClassConst {
			g.put1a(op, zr, zr, y.A)
		} else {
			g.load(y)
			g.put0(op, zr, zr, y.r)
			g.rh--
		}
		g.put2(opStr+v, zr, sp, x.A)
		g.rh--
	} else {
		g.loadAdr(x)
		zr := g.rh
		g.put2(opLdr+v, g.rh, x.r, 0)
		g.incR()
		if y.Mode == orb.ClassConst {
			g.put1a(op, zr, zr, y.A)
		} else {
			g.load(y)
			g.put0(op, zr, zr, y.r)
			g.rh--
		}
		g.put2(opStr+v, zr, x.r, 0)
		g.rh -= 2
	}
}

func (g *Generator) Include(inOrEx int32, x, y *Item) {
	g.loadAdr(x)
	zr := g.rh
	g.put2(opLdr, g.rh, x.r, 0)
	g.incR()
	var op int32
	if inOrEx == 0 {
		op = opIor
	} else {
		op = opAnn
	}
	if y.Mode == orb.ClassConst {
		g.put1a(op, zr, zr, 1<<y.A)
	} else {
		g.load(y)
		g.put1(opMov, g.rh, 0, 1)
		g.put0(opLsl, y.r, g.rh, y.r)
		g.put0(op, zr, zr, y.r)
		g.rh--
	}
	g.put2(opStr, zr, x.r, 0)
	g.rh -= 2
}

func (g *Generator) Assert(x *Item) {
	if x.Mode != classCond {
		g.loadCond(x)
	}
	var cond int32
	if x.A == 0 {
		cond = g.negated(x.r)
	} else {
		g.put3(opBC, x.r, x.B)
		g.FixLink(x.A)
		x.B = g.PC - 1
		cond = 7
	}
	g.trap(cond, 7)
	g.FixLink(x.B)
}

func (g *Generator) New(x *Item) {
	g.loadAdr(x)
	g.loadTypTagAdr(x.Type.Base)
	g.trap(7, 0)
	g.rh = 0
}

func (g *Generator) Pack(x, y *Item) {
	z := *x
	g.load(x)
	g.load(y)
	g.put1(opLsl, y.r, y.r, 23)
	g.put0(opAdd, x.r, x.r, y.r)
	g.rh--
	g.Store(&z, x)
}

func (g *Generator) Unpk(x, y *Item) {
	z := *x
	g.load(x)
	var e0 Item
	e0.Mode = classReg
	e0.r = g.rh
	e0.Type = g.orb.IntType
	g.put1(opAsr, g.rh, x.r, 23)
	g.put1(opSub, g.rh, g.rh, 127)
	g.Store(y, &e0)
	g.incR()
	g.put1(opLsl, g.rh, g.rh, 23)
	g.put0(opSub, x.r, x.r, g.rh)
	g.Store(&z, x)
}

func (g *Generator) Led(x *Item) {
	g.load(x)
	g.put1(opMov, g.rh, 0, -60)
	g.put2(opStr, x.r, g.rh, 0)
	g.rh--
}

func (g *Generator) Get(x, y *Item) {
	g.load(x)
	x.Type = y.Type
	x.Mode = classRegI
	x.A = 0
	g.Store(y, x)
}

func (g *Generator) Put(x, y *Item) {
	g.load(x)
	x.Type = y.Type
	x.Mode = classRegI
	x.A = 0
	g.Store(x, y)
}

func (g *Generator) Copy(x, y, z *Item) {
	g.load(x)
	g.load(y)
	if z.Mode == orb.ClassConst {
		if z.A > 0 {
			g.load(z)
		} else {
			g.ors.Mark("bad count")
		}
	} else {
		g.load(z)
		if g.check {
			g.trap(opLT, 3)
		}
		g.put3(opBC, opEQ, 6)
	}
	g.put2(opLdr, g.rh, x.r, 0)
	g.put1(opAdd, x.r, x.r, 4)
	g.put2(opStr, g.rh, y.r, 0)
	g.put1(opAdd, y.r, y.r, 4)
	g.put1(opSub, z.r, z.r, 1)
	g.put3(opBC, opNE, -6)
	g.rh -= 3
}

func (g *Generator) LDPSR(x *Item) {
	// x.Mode == ClassConst
	g.put3(0, 15, x.A+0x20)
}

func (g *Generator) LDREG(x, y *Item) {
	if y.Mode == orb.ClassConst {
		g.put1a(opMov, x.A, 0, y.A)
	} else {
		g.load(y)
		g.put0(opMov, x.A, 0, y.r)
		g.rh--
	}
}

// In-line code functions

func (g *Generator) Abs(x *Item) {
	if x.Mode == orb.ClassConst {
		x.A = abs(x.A)
	} else {
		g.load(x)
	}
	if x.Type.Form == orb.FormReal {
		g.put1(opLsl, x.r, x.r, 1)
		g.put1(opRor, x.r, x.r, 1)
	} else {
		g.put1(opCmp, x.r, x.r, 0)
		g.put3(opBC, opGE, 2)
		g.put1(opMov, g.rh, 0, 0)
		g.put0(opSub, x.r, g.rh, x.r)
	}
}

func abs(x int32) int32 {
	if x < 0 {
		return -x
	}
	return x
}

func (g *Generator) Odd(x *Item) {
	g.load(x)
	g.put1(opAnd, x.r, x.r, 1)
	g.setCC(x, opNE)
	g.rh--
}

func (g *Generator) Floor(x *Item) {
	g.load(x)
	g.put1(opMov+opU, g.rh, 0, 0x4B00)
	g.put0(opFad+opV, x.r, x.r, g.rh)
}

func (g *Generator) Float(x *Item) {
	g.load(x)
	g.put1(opMov+opU, g.rh, 0, 0x4B00)
	g.put0(opFad+opU, x.r, x.r, g.rh)
}

func (g *Generator) Ord(x *Item) {
	if x.Mode == orb.ClassVar || x.Mode == orb.ClassPar || x.Mode == classRegI || x.Mode == classCond {
		g.load(x)
	}
}

func (g *Generator) Len(x *Item) {
	if x.Type.Len >= 0 {
		if x.Mode == classRegI {
			g.rh--
		}
		x.Mode = orb.ClassConst
		x.A = x.Type.Len
	} else {
		// open array
		g.put2(opLdr, g.rh, sp, x.A+4+g.frame)
		x.Mode = classReg
		x.r = g.rh
		g.incR()
	}
}

func (g *Generator) Shift(fct int32, x, y *Item) {
	g.load(x)
	var op int32
	if fct == 0 {
		op = opLsl
	} else if fct == 1 {
		op = opAsr
	} else {
		op = opRor
	}
	if y.Mode == orb.ClassConst {
		g.put1(op, x.r, x.r, y.A&0x1F)
	} else {
		g.load(y)
		g.put0(op, g.rh-2, x.r, y.r)
		g.rh--
		x.r = g.rh - 1
	}
}

func (g *Generator) ADC(x, y *Item) {
	g.load(x)
	g.load(y)
	g.put0(opAdd+0x2000, x.r, x.r, y.r)
	g.rh--
}

func (g *Generator) SBC(x, y *Item) {
	g.load(x)
	g.load(y)
	g.put0(opSub+0x2000, x.r, x.r, y.r)
	g.rh--
}

func (g *Generator) UML(x, y *Item) {
	g.load(x)
	g.load(y)
	g.put0(opMul+0x2000, x.r, x.r, y.r)
	g.rh--
}

func (g *Generator) Bit(x, y *Item) {
	g.load(x)
	g.put2(opLdr, x.r, x.r, 0)
	if y.Mode == orb.ClassConst {
		g.put1(opRor, x.r, x.r, y.A+1)
		g.rh--
	} else {
		g.load(y)
		g.put1(opAdd, y.r, y.r, 1)
		g.put0(opRor, x.r, x.r, y.r)
		g.rh -= 2
	}
	g.setCC(x, opMI)
}

func (g *Generator) Register(x *Item) {
	// x.Mode == ClassConst
	g.put0(opMov, g.rh, 0, x.A%0x10)
	x.Mode = classReg
	x.r = g.rh
	g.incR()
}

func (g *Generator) H(x *Item) {
	// x.Mode == ClassConst
	g.put0(opMov+opU+x.A%2*opV, g.rh, 0, 0)
	x.Mode = classReg
	x.r = g.rh
	g.incR()
}

func (g *Generator) Adr(x *Item) {
	if x.Mode == orb.ClassVar || x.Mode == orb.ClassPar || x.Mode == classRegI {
		g.loadAdr(x)
	} else if (x.Mode == orb.ClassConst) && (x.Type.Form == orb.FormProc) {
		g.load(x)
	} else if (x.Mode == orb.ClassConst) && (x.Type.Form == orb.FormString) {
		g.loadStringAdr(x)
	} else {
		g.ors.Mark("not addressable")
	}
}

func (g *Generator) Condition(x *Item) {
	// x.Mode == ClassConst
	g.setCC(x, x.A)
}

func (g *Generator) Open(v int32) {
	g.PC = 0
	g.tdx = 0
	g.strx = 0
	g.rh = 0
	g.fixOrgP = 0
	g.fixOrgD = 0
	g.fixOrgT = 0
	g.check = v != 0
	g.version = v
	if v == 0 {
		for g.PC = 1; g.PC < 8; g.PC++ {
			g.code[g.PC] = 0
		}
	}
}

func (g *Generator) SetDataSize(dc int32) {
	g.varSize = dc
}

func (g *Generator) Header() {
	g.entry = g.PC * 4
	if g.version == 0 {
		// RISC-0
		i := 0xE7000000 - 1
		g.code[0] = int32(i) + g.PC
		g.put1a(opMov, sp, 0, stkOrg0)
	} else {
		g.put1(opSub, sp, sp, 4)
		g.put2(opStr, lnk, sp, 0)
	}
}

func (g *Generator) nOfPtrs(typ *orb.Type) (n int32) {
	if (typ.Form == orb.FormPointer) || (typ.Form == orb.FormNilTyp) {
		n = 1
	} else if typ.Form == orb.FormRecord {
		fld := typ.Dsc
		n = 0
		for fld != nil {
			n = g.nOfPtrs(fld.Type) + n
			fld = fld.Next
		}
	} else if typ.Form == orb.FormArray {
		n = g.nOfPtrs(typ.Base) * typ.Len
	} else {
		n = 0
	}
	return n
}

func (g *Generator) findPtrs(w io.ByteWriter, typ *orb.Type, adr int32) {
	if (typ.Form == orb.FormPointer) || (typ.Form == orb.FormNilTyp) {
		files.WriteInt(w, adr)
	} else if typ.Form == orb.FormRecord {
		fld := typ.Dsc
		for fld != nil {
			g.findPtrs(w, fld.Type, fld.Val+adr)
			fld = fld.Next
		}
	} else if typ.Form == orb.FormArray {
		s := typ.Base.Size
		for i := int32(0); i < typ.Len; i++ {
			g.findPtrs(w, typ.Base, i*s+adr)
		}
	}
}

func (g *Generator) Close(modId ors.Ident, key, nOfEnt int32) {
	// exit code
	if g.version == 0 {
		g.put1(opMov, 0, 0, 0)
		g.put3(opBR, 7, 0) // RISC-0
	} else {
		g.put2(opLdr, lnk, sp, 0)
		g.put1(opAdd, sp, sp, 4)
		g.put3(opBR, 7, lnk)
	}
	obj := g.orb.TopScope.Next
	nOfImps := 0
	comSize := 4
	nOfPtrs := int32(0)
	for obj != nil {
		if (obj.Class == orb.ClassMod) && (obj.Dsc != g.orb.System) {
			// count imports
			nOfImps++
		} else if (obj.ExNo != 0) && (obj.Class == orb.ClassConst) && (obj.Type.Form == orb.FormProc) &&
			(obj.Type.NOfPar == 0) && (obj.Type.Base == g.orb.NoType) {
			// count commands
			i := len(obj.Name)
			i = (i + 4) / 4 * 4
			comSize += i + 4
		} else if obj.Class == orb.ClassVar {
			// count pointers
			nOfPtrs += g.nOfPtrs(obj.Type)
		}
		obj = obj.Next
	}
	// varSize includes type descriptors
	size := g.varSize + g.strx + int32(comSize) + (g.PC+int32(nOfImps)+nOfEnt+nOfPtrs+1)*4

	// write code file
	name := string(modId) + ".rsc"
	f, err := os.Create(name)
	if err != nil {
		panic(err)
	}
	defer f.Close()
	w := bufio.NewWriter(f)
	files.WriteString(w, string(modId))
	files.WriteInt(w, key)
	files.Write(w, g.version)
	files.WriteInt(w, size)
	obj = g.orb.TopScope.Next
	// imports
	for obj != nil && obj.Class == orb.ClassMod {
		if obj.Dsc != g.orb.System {
			files.WriteString(w, string(obj.OrgName))
			files.WriteInt(w, obj.Val)
		}
		obj = obj.Next
	}
	files.Write(w, 0)
	files.WriteInt(w, g.tdx*4)
	// type descriptors
	for i := int32(0); i < g.tdx; i++ {
		files.WriteInt(w, g.data[i])
	}
	// data
	files.WriteInt(w, g.varSize-g.tdx*4)
	files.WriteInt(w, g.strx)
	// strings
	for i := int32(0); i < g.strx; i++ {
		files.WriteByte(w, g.str[i])
	}
	// code len
	files.WriteInt(w, g.PC)
	// program
	for i := int32(0); i < g.PC; i++ {
		files.WriteInt(w, g.code[i])
	}
	obj = g.orb.TopScope.Next
	// commands
	for obj != nil {
		if (obj.ExNo != 0) && (obj.Class == orb.ClassConst) && (obj.Type.Form == orb.FormProc) &&
			(obj.Type.NOfPar == 0) && (obj.Type.Base == g.orb.NoType) {

			files.WriteString(w, string(obj.Name))
			files.WriteInt(w, obj.Val)
		}
		obj = obj.Next
	}
	files.Write(w, 0)
	files.WriteInt(w, nOfEnt)
	files.WriteInt(w, g.entry)
	obj = g.orb.TopScope.Next
	// entries
	for obj != nil {
		if obj.ExNo != 0 {
			if ((obj.Class == orb.ClassConst) && (obj.Type.Form == orb.FormProc)) || (obj.Class == orb.ClassVar) {
				files.WriteInt(w, obj.Val)
			} else if obj.Class == orb.ClassTyp {
				if obj.Type.Form == orb.FormRecord {
					files.WriteInt(w, obj.Type.Len%0x10000)
				} else if (obj.Type.Form == orb.FormPointer) && ((obj.Type.Base.TypObj == nil) || (obj.Type.Base.TypObj.ExNo == 0)) {
					files.WriteInt(w, obj.Type.Base.Len%0x10000)
				}
			}
		}
		obj = obj.Next
	}
	obj = g.orb.TopScope.Next
	// pointer variables
	for obj != nil {
		if obj.Class == orb.ClassVar {
			g.findPtrs(w, obj.Type, obj.Val)
		}
		obj = obj.Next
	}
	files.WriteInt(w, -1)
	files.WriteInt(w, g.fixOrgP)
	files.WriteInt(w, g.fixOrgD)
	files.WriteInt(w, g.fixOrgT)
	files.WriteInt(w, g.entry)
	files.Write(w, 'O')
	err = w.Flush()
	if err != nil {
		panic(err)
	}
}

func log2(m int32, e *int32) int32 {
	*e = 0
	for m%2 == 0 {
		m /= 2
		*e++
	}
	return m
}
