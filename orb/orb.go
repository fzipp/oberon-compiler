// NW 25.6.2014  / AP 4.3.2020 / 8.3.2019  in Oberon-07
// Ported from Oberon to Go by Frederik Zipp, 2021.

// Package orb contains the "base" for the Oberon RISC compiler.
//
// Definition of data types Object and Type, which together form the data structure
// called "symbol table". Contains functions for creation of Objects, and for search:
// NewObj, ThisObj, ThisImport, ThisField (and OpenScope, CloseScope).
// Handling of import and export, i.e. reading and writing of "symbol files" is done by functions
// Import and Export. This package contains the list of standard identifiers, with which
// the symbol table (universe), and that of the pseudo-module SYSTEM are initialized.
package orb

import (
	"bufio"
	"bytes"
	"errors"
	"io"
	"io/fs"
	"os"

	"github.com/fzipp/oberon-compiler/files"
	"github.com/fzipp/oberon-compiler/ors"
)

const (
	VersionKey = 1
	maxTypTab  = 64
)

type Class byte

// class values
const (
	ClassHead Class = iota
	ClassConst
	ClassVar
	ClassPar
	ClassFld
	ClassTyp
	ClassSProc
	ClassSFunc
	ClassMod
)

type Form int

// form values; order is relevant
const (
	FormByte Form = 1 + iota
	FormBool
	FormChar
	FormInt
	FormReal
	FormSet
	FormPointer
	FormNilTyp
	FormNoTyp
	FormProc
	FormString
	FormArray
	FormRecord
)

type Object struct {
	Class   Class
	ExNo    byte
	Expo    bool // exported
	Rdo     bool // read-only
	Lev     int32
	Next    *Object
	Dsc     *Object
	Type    *Type
	Name    ors.Ident
	OrgName ors.Ident
	Val     int32
}

type Type struct {
	Form   Form
	Ref    Form // Ref is only used for import/export
	Mno    int32
	NOfPar int32 // for procedures, extension level for records
	Len    int32 // for arrays, len < 0 => open array; for records: adr of descriptor
	Dsc    *Object
	TypObj *Object
	Base   *Type // for arrays, records, pointers
	Size   int32 // in bytes; always multiple of 4, except for FormByte, FormBool and FormChar
}

// Object classes and the meaning of "Val":
//    Class         Val
//    -----------------------
//    ClassVar      address
//    ClassPar      address
//    ClassConst    value
//    ClassFld      offset
//    ClassTyp      type descriptor (TD) address
//    ClassSProc    inline code number
//    ClassSFunc    inline code number
//    ClassMod      key
//
//  Type forms and the meaning of "Dsc" and "Base":
//    Form         Dsc      Base
//    --------------------------------
//    FormPointer  -        type of dereferenced object
//    FormProc     params   result type
//    FormArray    -        type of elements
//    FormRecord   fields   extension

type Base struct {
	ors *ors.Scanner

	TopScope *Object
	universe *Object
	System   *Object

	ByteType *Type
	BoolType *Type
	CharType *Type
	IntType  *Type
	RealType *Type
	SetType  *Type
	NilType  *Type
	NoType   *Type
	StrType  *Type

	nOfMod int32
	ref    Form
	typTab [maxTypTab]*Type
}

func NewBase(s *ors.Scanner) *Base {
	b := &Base{ors: s}

	b.ByteType = b.newType(FormByte, FormInt, 1)
	b.BoolType = b.newType(FormBool, FormBool, 1)
	b.CharType = b.newType(FormChar, FormChar, 1)
	b.IntType = b.newType(FormInt, FormInt, 4)
	b.RealType = b.newType(FormReal, FormReal, 4)
	b.SetType = b.newType(FormSet, FormSet, 4)
	b.NilType = b.newType(FormNilTyp, FormNilTyp, 4)
	b.NoType = b.newType(FormNoTyp, FormNoTyp, 4)
	b.StrType = b.newType(FormString, FormString, 8)

	// initialize universe with data types and in-line procedures;
	// LONGINT is synonym to INTEGER, LONGREAL to REAL.
	// LED, ADC, SBC; LDPSR, LDREG, REG, COND are not in language definition
	b.System = nil
	// functions; n = procNo*10 + nOfPar
	b.enter("UML", ClassSFunc, b.IntType, 132)
	b.enter("SBC", ClassSFunc, b.IntType, 122)
	b.enter("ADC", ClassSFunc, b.IntType, 112)
	b.enter("ROR", ClassSFunc, b.IntType, 92)
	b.enter("ASR", ClassSFunc, b.IntType, 82)
	b.enter("LSL", ClassSFunc, b.IntType, 72)
	b.enter("LEN", ClassSFunc, b.IntType, 61)
	b.enter("CHR", ClassSFunc, b.CharType, 51)
	b.enter("ORD", ClassSFunc, b.IntType, 41)
	b.enter("FLT", ClassSFunc, b.RealType, 31)
	b.enter("FLOOR", ClassSFunc, b.IntType, 21)
	b.enter("ODD", ClassSFunc, b.BoolType, 11)
	b.enter("ABS", ClassSFunc, b.IntType, 1)
	// procedures
	b.enter("LED", ClassSProc, b.NoType, 81)
	b.enter("UNPK", ClassSProc, b.NoType, 72)
	b.enter("PACK", ClassSProc, b.NoType, 62)
	b.enter("NEW", ClassSProc, b.NoType, 51)
	b.enter("ASSERT", ClassSProc, b.NoType, 41)
	b.enter("EXCL", ClassSProc, b.NoType, 32)
	b.enter("INCL", ClassSProc, b.NoType, 22)
	b.enter("DEC", ClassSProc, b.NoType, 11)
	b.enter("INC", ClassSProc, b.NoType, 1)
	// types
	b.enter("SET", ClassTyp, b.SetType, 0)
	b.enter("BOOLEAN", ClassTyp, b.BoolType, 0)
	b.enter("BYTE", ClassTyp, b.ByteType, 0)
	b.enter("CHAR", ClassTyp, b.CharType, 0)
	b.enter("LONGREAL", ClassTyp, b.RealType, 0)
	b.enter("REAL", ClassTyp, b.RealType, 0)
	b.enter("LONGINT", ClassTyp, b.IntType, 0)
	b.enter("INTEGER", ClassTyp, b.IntType, 0)
	b.TopScope = nil
	b.OpenScope()
	b.TopScope.Next = b.System
	b.universe = b.TopScope

	// initialize "unsafe" pseudo-module SYSTEM
	b.System = nil
	// functions
	b.enter("H", ClassSFunc, b.IntType, 201)
	b.enter("COND", ClassSFunc, b.BoolType, 191)
	b.enter("SIZE", ClassSFunc, b.IntType, 181)
	b.enter("ADR", ClassSFunc, b.IntType, 171)
	b.enter("VAL", ClassSFunc, b.IntType, 162)
	b.enter("REG", ClassSFunc, b.IntType, 151)
	b.enter("BIT", ClassSFunc, b.BoolType, 142)
	// procedures
	b.enter("LDREG", ClassSProc, b.NoType, 142)
	b.enter("LDPSR", ClassSProc, b.NoType, 131)
	b.enter("COPY", ClassSProc, b.NoType, 123)
	b.enter("PUT", ClassSProc, b.NoType, 112)
	b.enter("GET", ClassSProc, b.NoType, 102)

	return b
}

func (b *Base) NewObj(id ors.Ident, class Class) (obj *Object) {
	// insert new Object with name id
	x := b.TopScope
	for x.Next != nil && x.Next.Name != id {
		x = x.Next
	}
	if x.Next == nil {
		obj = &Object{
			Name:  id,
			Class: class,
			Next:  nil,
			Rdo:   false,
			Dsc:   nil,
		}
		x.Next = obj
	} else {
		obj = x.Next
		b.ors.Mark("mult def")
	}
	return obj
}

func (b *Base) ThisObj() (x *Object) {
	s := b.TopScope
	for {
		x = s.Next
		for x != nil && x.Name != b.ors.Id {
			x = x.Next
		}
		s = s.Dsc
		if x != nil || s == nil {
			break
		}
	}
	return x
}

func (b *Base) ThisImport(mod *Object) (obj *Object) {
	if mod.Rdo {
		if mod.Name != "" {
			obj = mod.Dsc
			for (obj != nil) && (obj.Name != b.ors.Id) {
				obj = obj.Next
			}
		} else {
			obj = nil
		}
	} else {
		obj = nil
	}
	return obj
}

func (b *Base) ThisField(rec *Type) *Object {
	fld := rec.Dsc
	for (fld != nil) && (fld.Name != b.ors.Id) {
		fld = fld.Next
	}
	return fld
}

func (b *Base) OpenScope() {
	b.TopScope = &Object{
		Class: ClassHead,
		Dsc:   b.TopScope,
		Next:  nil,
	}
}

func (b *Base) CloseScope() {
	b.TopScope = b.TopScope.Dsc
}

// ------------------------------- Import ---------------------------------

func (b *Base) thisModule(name, orgName ors.Ident, decl bool, key int32) *Object {
	// search for module
	obj1 := b.TopScope
	obj := obj1.Next
	for (obj != nil) && (obj.OrgName != orgName) {
		obj1 = obj
		obj = obj1.Next
	}
	if obj == nil {
		// new module, search for alias
		obj = b.TopScope.Next
		for (obj != nil) && (obj.Name != name) {
			obj = obj.Next
		}
		if obj == nil {
			// insert new module
			mod := &Object{
				Class:   ClassMod,
				Rdo:     false,
				Name:    name,
				OrgName: orgName,
				Val:     key,
				Lev:     b.nOfMod,
				Dsc:     nil,
				Next:    nil,
			}
			b.nOfMod++
			if decl {
				mod.Type = b.NoType
			} else {
				mod.Type = b.NilType
			}
			obj1.Next = mod
			obj = mod
		} else if decl {
			if obj.Type.Form == FormNoTyp {
				b.ors.Mark("mult def")
			} else {
				b.ors.Mark("invalid import order")
			}
		} else {
			b.ors.Mark("conflict with alias")
		}
	} else if decl {
		// module already present, explicit import by declaration
		if obj.Type.Form == FormNoTyp {
			b.ors.Mark("mult def")
		} else {
			b.ors.Mark("invalid import order")
		}
	}
	return obj
}

func (b *Base) inType(r *bufio.Reader, thisMod *Object) (t *Type) {
	ref := files.Read(r)
	if ref < 0 {
		// already read
		t = b.typTab[-ref]
	} else {
		form := Form(files.Read(r))
		t = &Type{
			Mno:  thisMod.Lev,
			Form: form,
		}
		b.typTab[ref] = t
		if form == FormPointer {
			t.Base = b.inType(r, thisMod)
			t.Size = 4
		} else if form == FormArray {
			t.Base = b.inType(r, thisMod)
			t.Len = files.ReadNum(r)
			t.Size = files.ReadNum(r)
		} else if form == FormRecord {
			t.Base = b.inType(r, thisMod)
			var obj *Object
			if t.Base.Form == FormNoTyp {
				t.Base = nil
				obj = nil
			} else {
				obj = t.Base.Dsc
			}
			t.Len = files.ReadNum(r)    // TD adr/exno
			t.NOfPar = files.ReadNum(r) // ext level
			t.Size = files.ReadNum(r)
			class := Class(files.Read(r))
			var last *Object
			for class != 0 {
				// fields
				fld := &Object{
					Class: class,
					Name:  ors.Ident(files.ReadString(r)),
				}
				if last == nil {
					t.Dsc = fld
				} else {
					last.Next = fld
				}
				last = fld
				if fld.Name != "" {
					fld.Expo = true
					fld.Type = b.inType(r, thisMod)
				} else {
					fld.Expo = false
					fld.Type = b.NilType
				}
				fld.Val = files.ReadNum(r)
				class = Class(files.Read(r))
			}
			if last == nil {
				t.Dsc = obj
			} else {
				last.Next = obj
			}
		} else if form == FormProc {
			t.Base = b.inType(r, thisMod)
			var obj *Object
			np := int32(0)
			class := Class(files.Read(r))
			for class != 0 {
				// parameters
				par := &Object{
					Class: class,
					Rdo:   files.Read(r) == 1,
					Type:  b.inType(r, thisMod),
					Next:  obj,
				}
				obj = par
				np++
				class = Class(files.Read(r))
			}
			t.Dsc = obj
			t.NOfPar = np
			t.Size = 4
		}
		modName := ors.Ident(files.ReadString(r))
		if modName != "" {
			// re-import ========
			key := files.ReadInt(r)
			name := ors.Ident(files.ReadString(r))
			mod := b.thisModule(modName, modName, false, key)
			// search type
			obj := mod.Dsc
			for (obj != nil) && (obj.Name != name) {
				obj = obj.Next
			}
			if obj != nil {
				// type object found in object list of mod
				t = obj.Type
			} else {
				// insert new type object in object list of mod
				obj = &Object{
					Name:  name,
					Class: ClassTyp,
					Next:  mod.Dsc,
					Type:  t,
				}
				mod.Dsc = obj
				t.Mno = mod.Lev
				t.TypObj = obj
			}
			b.typTab[ref] = t
		}
	}
	return t
}

func (b *Base) Import(modId, modId1 ors.Ident) {
	if modId1 == "SYSTEM" {
		thisMod := b.thisModule(modId, modId1, true, 0)
		b.nOfMod--
		thisMod.Lev = 0
		thisMod.Dsc = b.System
		thisMod.Rdo = true
	} else {
		fname := string(modId1) + ".smb"
		f, err := os.Open(fname)
		if err == nil {
			defer f.Close()
			r := bufio.NewReader(f)
			_ = files.ReadInt(r)
			key := files.ReadInt(r)
			modName := files.ReadString(r)
			_ = modName
			thisMod := b.thisModule(modId, modId1, true, key)
			thisMod.Rdo = true
			versionKey := files.Read(r) // version key
			if versionKey != VersionKey {
				b.ors.Mark("wrong version")
			}
			class := Class(files.Read(r))
			for class != 0 {
				obj := &Object{
					Class: class,
					Name:  ors.Ident(files.ReadString(r)),
					Type:  b.inType(r, thisMod),
					Lev:   -thisMod.Lev,
				}
				if class == ClassTyp {
					t := obj.Type
					t.TypObj = obj
					// fixup bases of previously declared pointer types
					k := files.Read(r)
					for k != 0 {
						b.typTab[k].Base = t
						k = files.Read(r)
					}
				} else {
					if class == ClassConst {
						if obj.Type.Form == FormReal {
							obj.Val = files.ReadInt(r)
						} else {
							obj.Val = files.ReadNum(r)
						}
					} else if class == ClassVar {
						obj.Val = files.ReadNum(r)
						obj.Rdo = true
					}
				}
				obj.Next = thisMod.Dsc
				thisMod.Dsc = obj
				class = Class(files.Read(r))
			}
		} else {
			b.ors.Mark("import not available")
		}
	}
}

// -------------------------------- Export ---------------------------------

func (b *Base) outPar(w io.ByteWriter, par *Object, n int32) {
	if n > 0 {
		b.outPar(w, par.Next, n-1)
		cl := par.Class
		files.Write(w, int32(cl))
		if par.Rdo {
			files.Write(w, 1)
		} else {
			files.Write(w, 0)
		}
		b.outType(w, par.Type)
	}
}

func (b *Base) findHiddenPointers(w io.ByteWriter, typ *Type, offset int32) {
	if (typ.Form == FormPointer) || (typ.Form == FormNilTyp) {
		files.Write(w, int32(ClassFld))
		files.Write(w, 0)
		files.WriteNum(w, offset)
	} else if typ.Form == FormRecord {
		fld := typ.Dsc
		for fld != nil {
			b.findHiddenPointers(w, fld.Type, fld.Val+offset)
			fld = fld.Next
		}
	} else if typ.Form == FormArray {
		i := int32(0)
		n := typ.Len
		for i < n {
			b.findHiddenPointers(w, typ.Base, typ.Base.Size*i+offset)
			i++
		}
	}
}

func (b *Base) outType(w io.ByteWriter, t *Type) {
	if t.Ref > 0 {
		// type was already output
		files.Write(w, int32(-t.Ref))
	} else {
		obj := t.TypObj
		if obj != nil {
			files.Write(w, int32(b.ref))
			t.Ref = b.ref
			b.ref++
		} else {
			// anonymous
			files.Write(w, 0)
		}
		files.Write(w, int32(t.Form))
		if t.Form == FormPointer {
			b.outType(w, t.Base)
		} else if t.Form == FormArray {
			b.outType(w, t.Base)
			files.WriteNum(w, t.Len)
			files.WriteNum(w, t.Size)
		} else if t.Form == FormRecord {
			var bot *Object
			if t.Base != nil {
				b.outType(w, t.Base)
				bot = t.Base.Dsc
			} else {
				b.outType(w, b.NoType)
				bot = nil
			}
			if obj != nil {
				files.WriteNum(w, int32(obj.ExNo))
			} else {
				files.Write(w, 0)
			}
			files.WriteNum(w, t.NOfPar)
			files.WriteNum(w, t.Size)
			fld := t.Dsc
			// fields
			for fld != bot {
				if fld.Expo {
					files.Write(w, int32(ClassFld))
					files.WriteString(w, string(fld.Name))
					b.outType(w, fld.Type)
					files.WriteNum(w, fld.Val) // offset
				} else {
					b.findHiddenPointers(w, fld.Type, fld.Val)
				}
				fld = fld.Next
			}
			files.Write(w, 0)
		} else if t.Form == FormProc {
			b.outType(w, t.Base)
			b.outPar(w, t.Dsc, t.NOfPar)
			files.Write(w, 0)
		}
		if (t.Mno > 0) && (obj != nil) {
			// re-export, output name
			mod := b.TopScope.Next
			for (mod != nil) && (mod.Lev != t.Mno) {
				mod = mod.Next
			}
			if mod != nil {
				files.WriteString(w, string(mod.OrgName))
				files.WriteInt(w, mod.Val)
				files.WriteString(w, string(obj.Name))
			} else {
				b.ors.Mark("re-export not found")
				files.Write(w, 0)
			}
		} else {
			files.Write(w, 0)
		}
	}
}

func (b *Base) Export(modId ors.Ident, newSF bool) (int32, bool) {
	b.ref = FormRecord + 1
	w := &bytes.Buffer{}
	files.WriteInt(w, 0) // placeholder
	files.WriteInt(w, 0) // placeholder for key to be inserted at the end
	files.WriteString(w, string(modId))
	files.Write(w, VersionKey)
	obj := b.TopScope.Next
	for obj != nil {
		if obj.Expo {
			files.Write(w, int32(obj.Class))
			files.WriteString(w, string(obj.Name))
			b.outType(w, obj.Type)
			if obj.Class == ClassTyp {
				if obj.Type.Form == FormRecord {
					// check whether this is base of previously declared pointer types
					obj0 := b.TopScope.Next
					for obj0 != obj {
						if (obj0.Type.Form == FormPointer) && (obj0.Type.Base == obj.Type) && (obj0.Type.Ref > 0) {
							files.Write(w, int32(obj0.Type.Ref))
						}
						obj0 = obj0.Next
					}
				}
				files.Write(w, 0)
			} else if obj.Class == ClassConst {
				if obj.Type.Form == FormProc {
					files.WriteNum(w, int32(obj.ExNo))
				} else if obj.Type.Form == FormReal {
					files.WriteInt(w, obj.Val)
				} else {
					files.WriteNum(w, obj.Val)
				}
			} else if obj.Class == ClassVar {
				files.WriteNum(w, int32(obj.ExNo))
			}
		}
		obj = obj.Next
	}
	padLen := 4 - int(w.Len()%4)
	for range padLen {
		files.Write(w, 0)
	}
	for b.ref = FormRecord + 1; b.ref < maxTypTab; b.ref++ {
		b.typTab[b.ref] = nil
	}
	// compute key (checksum)
	r := bytes.NewReader(w.Bytes())
	sum := int32(0)
	x, err := files.ReadIntWithEOF(r)
	for err != io.EOF {
		sum += x
		x, err = files.ReadIntWithEOF(r)
	}
	// insert checksum
	sumBuf := bytes.Buffer{}
	files.WriteInt(&sumBuf, sum)
	copy(w.Bytes()[4:], sumBuf.Bytes())
	filename := string(modId) + ".smb"
	oldKey, err := readKey(filename)
	notExist := errors.Is(err, fs.ErrNotExist)
	if notExist {
		oldKey = sum + 1
	} else if err != nil {
		panic(err)
	}
	if sum != oldKey {
		if newSF || notExist {
			f, err2 := os.Create(filename)
			if err2 != nil {
				panic(err2)
			}
			defer f.Close()
			_, err2 = io.Copy(f, w)
			if err2 != nil {
				panic(err2)
			}
			return sum, true
		} else {
			b.ors.Mark("new symbol file inhibited")
		}
	}
	return sum, false
}

func readKey(smbFilename string) (key int32, err error) {
	f, err := os.Open(smbFilename)
	if err != nil {
		return 0, err
	}
	defer f.Close()
	_ = files.ReadInt(f)
	key = files.ReadInt(f)
	return key, nil
}

func (b *Base) Init() {
	b.TopScope = b.universe
	b.nOfMod = 1
}

func (b *Base) newType(ref, form Form, size int32) *Type {
	tp := &Type{
		Form: form,
		Size: size,
		Ref:  ref,
		Base: nil,
	}
	b.typTab[ref] = tp
	return tp
}

func (b *Base) enter(name ors.Ident, cl Class, typ *Type, n int32) {
	obj := &Object{
		Name:  name,
		Class: cl,
		Type:  typ,
		Val:   n,
		Dsc:   nil,
	}
	if cl == ClassTyp {
		typ.TypObj = obj
	}
	obj.Next = b.System
	b.System = obj
}
