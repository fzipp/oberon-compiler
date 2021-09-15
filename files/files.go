package files

import (
	"bytes"
	"encoding/binary"
	"io"
	"math/bits"
)

var byteOrder = binary.LittleEndian

func Read(r io.ByteReader) int32 {
	b := ReadByte(r)
	if b < 0x80 {
		return int32(b)
	}
	return int32(b) - 0x100
}

func ReadByte(r io.ByteReader) byte {
	b, err := r.ReadByte()
	if err != nil {
		panic(err)
	}
	return b
}

func ReadInt(r io.Reader) int32 {
	var i int32
	err := binary.Read(r, byteOrder, &i)
	if err != nil {
		panic(err)
	}
	return i
}

func ReadIntWithEOF(r io.Reader) (int32, error) {
	var i int32
	err := binary.Read(r, byteOrder, &i)
	if err != nil {
		if err == io.EOF {
			return i, err
		}
		panic(err)
	}
	return i, nil
}

func ReadNum(r io.ByteReader) (x int32) {
	n := 32
	y := 0
	b := ReadByte(r)
	for b >= 0x80 {
		y = int(bits.RotateLeft32(uint32(y+int(b)-0x80), -7))
		n -= 7
		b = ReadByte(r)
	}
	if n <= 4 {
		x = int32(bits.RotateLeft32(uint32(y+int(b)%0x10), -4))
	} else {
		x = int32(int32(bits.RotateLeft32(uint32(y+int(b)), -7)) >> (n - 7))
	}
	return x
}

func ReadString(r io.ByteReader) string {
	var buf bytes.Buffer
	for {
		b := ReadByte(r)
		if b == 0 {
			break
		}
		buf.WriteByte(b)
	}
	return buf.String()
}

func WriteString(w io.ByteWriter, x string) {
	for _, b := range []byte(x) {
		WriteByte(w, b)
	}
	WriteByte(w, 0)
}

func WriteInt(w io.ByteWriter, x int32) {
	buf := make([]byte, 4)
	byteOrder.PutUint32(buf[:], uint32(x))
	for _, b := range buf {
		WriteByte(w, b)
	}
}

func Write(w io.ByteWriter, ch int32) {
	WriteByte(w, byte(ch))
}

func WriteByte(w io.ByteWriter, ch byte) {
	err := w.WriteByte(ch)
	if err != nil {
		panic(err)
	}
}

func WriteNum(w io.ByteWriter, x int32) {
	for (x < -0x40) || (x >= 0x40) {
		WriteByte(w, byte(x)%0x80+0x80)
		x = x >> 7
	}
	WriteByte(w, byte(x)%0x80)
}
