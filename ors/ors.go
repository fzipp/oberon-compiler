// NW 19.9.93 / 15.3.2017  Scanner in Oberon-07
// Ported from Oberon to Go by Frederik Zipp, 2021.

// Package ors contains the lexical scanner for the Oberon RISC compiler.
package ors

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"math"
)

const (
	IdLen         = 32
	maxExp        = 38
	stringBufSize = 256
)

// Scanner does lexical analysis. Input is Oberon-Text, output is
// sequence of symbols, i.e. identifiers, numbers, strings, and special symbols.
// Recognises all Oberon keywords and skips comments. The keywords are
// recorded in a table (map).
// Get delivers next symbol from input text with Reader r.
// Mark records error and delivers error message with Writer w.
// If Get delivers SymIdent, then the identifier (a string) is in field Id,
// if SymInt or SymChar in Ival, if SymReal in Rval, and if SymString in Str.
type Scanner struct {
	// results of Get
	Ival   int32
	Rval   float32
	Id     Ident // for identifiers
	Str    []byte
	ErrCnt int

	ch     byte // last character read
	eot    bool
	errPos int
	pos    int
	r      io.ByteReader
	w      io.Writer
}

func NewScanner(r io.Reader, w io.Writer) *Scanner {
	return &Scanner{
		r: bufio.NewReader(r),
		w: w,
	}
}

func (s *Scanner) Pos() int {
	return s.pos - 1
}

func (s *Scanner) Mark(msg string) {
	p := s.Pos()
	if p > s.errPos && s.ErrCnt < 25 {
		_, err := fmt.Fprintf(s.w, "\n  pos %d %s", p, msg)
		if err != nil {
			panic(err)
		}
	}
	s.ErrCnt++
	s.errPos = p + 4
}

func (s *Scanner) nextCh() {
	var err error
	s.ch, err = s.r.ReadByte()
	s.pos++
	if err != nil {
		if err == io.EOF {
			s.eot = true
			return
		}
		panic(err)
	}
}

func (s *Scanner) identifier() (sym Sym) {
	var buf bytes.Buffer
	for {
		if buf.Len() < IdLen-1 {
			buf.WriteByte(s.ch)
		}
		s.nextCh()
		if (s.ch < '0' || s.ch > '9') && (s.ch < 'A' || s.ch > 'Z') && (s.ch < 'a' || s.ch > 'z') {
			break
		}
	}
	s.Id = Ident(buf.String())
	// lookup keyword
	if kwSym, ok := keyTab[s.Id]; ok {
		sym = kwSym
	} else {
		sym = SymIdent
	}
	return sym
}

func (s *Scanner) string() {
	s.nextCh()
	var buf bytes.Buffer
	for !s.eot && s.ch != '"' {
		if s.ch >= ' ' {
			if buf.Len() < stringBufSize-1 {
				buf.WriteByte(s.ch)
			} else {
				s.Mark("string too long")
			}
		}
		s.nextCh()
	}
	buf.WriteByte(0)
	s.Str = buf.Bytes()
	s.nextCh()
}

func (s *Scanner) hexString() {
	s.nextCh()
	var buf bytes.Buffer
	for !s.eot && s.ch != '$' {
		for !s.eot && s.ch <= ' ' { // skip
			s.nextCh()
		}
		m := s.hexDigit()
		s.nextCh()
		n := s.hexDigit()
		if buf.Len() < stringBufSize {
			buf.WriteByte(byte(m*0x10 + n))
		} else {
			s.Mark("string too long")
		}
		s.nextCh()
	}
	// no '\0' appended!
	s.Str = buf.Bytes()
	s.nextCh()
}

func (s *Scanner) hexDigit() (n int) {
	if '0' <= s.ch && s.ch <= '9' {
		return int(s.ch) - 0x30
	}
	if 'A' <= s.ch && s.ch <= 'F' {
		return int(s.ch) - 0x37
	}
	s.Mark("hexdig expected")
	return 0
}

func ten(e int) float32 {
	x := float32(1.0)
	t := float32(10.0)
	for e > 0 {
		if e%2 != 0 {
			x = t * x
		}
		t = t * t
		e = e / 2
	}
	return x
}

func (s *Scanner) number() (sym Sym) {
	s.Ival = 0
	d := make([]int, 0, 16)
	for {
		if len(d) < 16 {
			d = append(d, int(s.ch)-0x30)
		} else {
			s.Mark("too many digits")
			d = d[:0]
		}
		s.nextCh()
		if (s.ch < '0' || s.ch > '9') && (s.ch < 'A' || s.ch > 'F') {
			break
		}
	}
	if s.ch == 'H' || s.ch == 'R' || s.ch == 'X' { // hex
		k := 0
		for _, h := range d {
			if h >= 10 {
				h -= 7
			}
			k = k*0x10 + h // no overflow check
		}
		if s.ch == 'X' {
			sym = SymChar
			if k < 0x100 {
				s.Ival = int32(k)
			} else {
				s.Mark("illegal value")
				s.Ival = 0
			}
		} else if s.ch == 'R' {
			sym = SymReal
			s.Rval = math.Float32frombits(uint32(k))
		} else {
			sym = SymInt
			s.Ival = int32(k)
		}
		s.nextCh()
	} else if s.ch == '.' {
		s.nextCh()
		if s.ch == '.' { // double dot
			s.ch = 0x7F
			// decimal integer
			sym = SymInt
			s.Ival = int32(s.decimalInteger(d))
		} else {
			// real number
			x := float32(0)
			e := 0
			for _, dd := range d { // integer part
				x = x*10.0 + float32(dd)
			}
			for s.ch >= '0' && s.ch <= '9' { // fraction
				x = x*10.0 + float32(s.ch-0x30)
				e--
				s.nextCh()
			}
			var negE bool
			if s.ch == 'E' || s.ch == 'D' { // scale factor
				s.nextCh()
				sf := 0
				if s.ch == '-' {
					negE = true
					s.nextCh()
				} else {
					negE = false
					if s.ch == '+' {
						s.nextCh()
					}
				}
				if s.ch >= '0' && s.ch <= '9' {
					for {
						sf = sf*10 + (int(s.ch) - 0x30)
						s.nextCh()
						if s.ch < '0' || s.ch > '9' {
							break
						}
					}
					if negE {
						e -= sf
					} else {
						e += sf
					}
				} else {
					s.Mark("digit?")
				}
			}
			if e < 0 {
				if e >= -maxExp {
					x = x / ten(-e)
				} else {
					x = 0.0
				}
			} else if e > 0 {
				if e <= maxExp {
					x = ten(e) * x
				} else {
					x = 0.0
					s.Mark("too large")
				}
			}
			sym = SymReal
			s.Rval = x
		}
	} else {
		// decimal integer
		sym = SymInt
		s.Ival = int32(s.decimalInteger(d))
	}
	return sym
}

func (s *Scanner) decimalInteger(digits []int) (k int) {
	const max = 2147483647 // 2^31 - 1
	for _, d := range digits {
		if d < 10 {
			if k <= (max-d)/10 {
				k = k*10 + d
			} else {
				s.Mark("too large")
				k = 0
			}
		} else {
			s.Mark("bad integer")
		}
	}
	return k
}

func (s *Scanner) comment() {
	s.nextCh()
	for {
		for !s.eot && s.ch != '*' {
			if s.ch == '(' {
				s.nextCh()
				if s.ch == '*' {
					s.comment()
				}
			} else {
				s.nextCh()
			}
		}
		for s.ch == '*' {
			s.nextCh()
		}
		if s.ch == ')' || s.eot {
			break
		}
	}
	if !s.eot {
		s.nextCh()
	} else {
		s.Mark("unterminated comment")
	}
}

func (s *Scanner) Get() (sym Sym) {
	for sym == symNull {
		for !s.eot && s.ch <= ' ' {
			s.nextCh()
		}
		if s.eot {
			sym = SymEot
		} else if s.ch < 'A' {
			if s.ch < '0' {
				switch s.ch {
				case '"':
					s.string()
					sym = SymString
				case '#':
					s.nextCh()
					sym = SymNeq
				case '$':
					s.hexString()
					sym = SymString
				case '&':
					s.nextCh()
					sym = SymAnd
				case '(':
					s.nextCh()
					if s.ch == '*' {
						sym = symNull
						s.comment()
					} else {
						sym = SymLparen
					}
				case ')':
					s.nextCh()
					sym = SymRparen
				case '*':
					s.nextCh()
					sym = SymTimes
				case '+':
					s.nextCh()
					sym = SymPlus
				case ',':
					s.nextCh()
					sym = SymComma
				case '-':
					s.nextCh()
					sym = SymMinus
				case '.':
					s.nextCh()
					if s.ch == '.' {
						s.nextCh()
						sym = SymUpto
					} else {
						sym = SymPeriod
					}
				case '/':
					s.nextCh()
					sym = SymRdiv
				default:
					// ! % '
					s.nextCh()
				}
			} else if s.ch < ':' {
				sym = s.number()
			} else if s.ch == ':' {
				s.nextCh()
				if s.ch == '=' {
					s.nextCh()
					sym = SymBecomes
				} else {
					sym = SymColon
				}
			} else if s.ch == ';' {
				s.nextCh()
				sym = SymSemicolon
			} else if s.ch == '<' {
				s.nextCh()
				if s.ch == '=' {
					s.nextCh()
					sym = SymLeq
				} else {
					sym = SymLss
				}
			} else if s.ch == '=' {
				s.nextCh()
				sym = SymEql
			} else if s.ch == '>' {
				s.nextCh()
				if s.ch == '=' {
					s.nextCh()
					sym = SymGeq
				} else {
					sym = SymGtr
				}
			} else {
				// ? @
				s.nextCh()
				sym = symNull
			}
		} else if s.ch < '[' {
			sym = s.identifier()
		} else if s.ch < 'a' {
			switch s.ch {
			case '[':
				sym = SymLbrak
			case ']':
				sym = SymRbrak
			case '^':
				sym = SymArrow
			default:
				// _ `
				sym = symNull
			}
			s.nextCh()
		} else if s.ch < '{' {
			sym = s.identifier()
		} else {
			switch s.ch {
			case '{':
				sym = SymLbrace
			case '}':
				sym = SymRbrace
			case '|':
				sym = SymBar
			case '~':
				sym = SymNot
			case 0x7F:
				sym = SymUpto
			default:
				sym = symNull
			}
			s.nextCh()
		}
	}
	return sym
}

type Sym int

// lexical symbols; order is relevant
const (
	symNull Sym = iota
	SymTimes
	SymRdiv
	SymDiv
	SymMod
	SymAnd
	SymPlus
	SymMinus
	SymOr
	SymEql
	SymNeq
	SymLss
	SymLeq
	SymGtr
	SymGeq
	SymIn
	SymIs
	SymArrow
	SymPeriod
	SymChar
	SymInt
	SymReal
	SymFalse
	SymTrue
	SymNil
	SymString
	SymNot
	SymLparen
	SymLbrak
	SymLbrace
	SymIdent
	SymIf
	SymWhile
	SymRepeat
	SymCase
	SymFor
	SymComma
	SymColon
	SymBecomes
	SymUpto
	SymRparen
	SymRbrak
	SymRbrace
	SymThen
	SymOf
	SymDo
	SymTo
	SymBy
	SymSemicolon
	SymEnd
	SymBar
	SymElse
	SymElsif
	SymUntil
	SymReturn
	SymArray
	SymRecord
	SymPointer
	SymConst
	SymType
	SymVar
	SymProcedure
	SymBegin
	SymImport
	SymModule
	SymEot
)

type Ident string

var keyTab = map[Ident]Sym{
	"ARRAY":     SymArray,
	"BEGIN":     SymBegin,
	"BY":        SymBy,
	"CASE":      SymCase,
	"CONST":     SymConst,
	"DIV":       SymDiv,
	"DO":        SymDo,
	"ELSE":      SymElse,
	"ELSIF":     SymElsif,
	"END":       SymEnd,
	"FALSE":     SymFalse,
	"FOR":       SymFor,
	"IF":        SymIf,
	"IMPORT":    SymImport,
	"IN":        SymIn,
	"IS":        SymIs,
	"MOD":       SymMod,
	"MODULE":    SymModule,
	"NIL":       SymNil,
	"OF":        SymOf,
	"OR":        SymOr,
	"POINTER":   SymPointer,
	"PROCEDURE": SymProcedure,
	"RECORD":    SymRecord,
	"REPEAT":    SymRepeat,
	"RETURN":    SymReturn,
	"THEN":      SymThen,
	"TO":        SymTo,
	"TRUE":      SymTrue,
	"TYPE":      SymType,
	"UNTIL":     SymUntil,
	"VAR":       SymVar,
	"WHILE":     SymWhile,
}
