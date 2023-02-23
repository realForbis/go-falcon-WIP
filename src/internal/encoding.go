package internal

/*
Compression and decompression routines for signatures.
*/

import (
	"errors"
	"fmt"
	"math"
	"strconv"
	"strings"

	_ "github.com/realForbis/go-falcon/src/types"
)

var (
	ErrEncodingTooLong = errors.New("encoding is too long")
	ErrInvalidEncoding = errors.New("invalid encoding")
)

// Take as input an array of integers v and a bytelength slen, and
// return a bytestring of length slen that encode/compress v.
// If this is not possible, return False.
//
// For each coefficient of v:
// - the sign is encoded on 1 bit
// - the 7 lower bits are encoded naively (binary)
// - the high bits are encoded in unary encoding
func Compress(v []int16, slen int) ([]byte, error) {
	var u string
	for _, coef := range v {
		// Encode the sign
		s := "1"
		if coef >= 0 {
			s = "0"
		}
		// Encode the low bits
		s += fmt.Sprintf("%09b", int(math.Mod(math.Abs(float64(coef)), 1<<7)))[2:]
		// Encode the high bits
		s += strings.Repeat("0", int(math.Abs(float64(coef)))/(1<<7)) + "1"
		u += s
	}
	// The encoding is too long
	if len(u) > 8*slen {
		return nil, ErrEncodingTooLong
	}
	u += strings.Repeat("0", 8*slen-len(u))
	w := make([]int, len(u)/8)
	for i := 0; i < len(u)/8; i++ {
		val, _ := strconv.ParseInt(u[8*i:8*i+8], 2, 64)
		w[i] = int(val)
	}
	x := make([]byte, len(w))
	for i, val := range w {
		x[i] = byte(val)
	}
	return x, nil
}

// Take as input an encoding x, a bytelength slen and a length n, and
// return a list of integers v of length n such that x encode v.
// If such a list does not exist, the encoding is invalid and we output (nil, ErrInvalidEncoding).
func Decompress(x []byte, slen int, n int) ([]int, error) {
	var u string
	if len(x) > slen {
		return nil, ErrInvalidEncoding
	}
	for _, elt := range x {
		u += strconv.FormatInt(256^int64(elt), 2)[1:]
	}
	v := []int{}
	for u[len(u)-1:] == "0" {
		u = u[:len(u)-1]
	}
	for u != "" && len(v) < n {
		// Recover the sign of coef
		sign := -1
		if u[:1] == "1" {
			sign = -1
		} else {
			sign = 1
		}
		low, _ := strconv.ParseInt(u[1:8], 2, 64)
		i, high := 8, 0
		for u[i:i+1] == "0" {
			i++
			high++
		}
		// Compute coef
		coef := sign * (int(low) + (high << 7))
		// Enforce a unique encoding for coef = 0
		if coef == 0 && sign == -1 {
			return nil, ErrInvalidEncoding
		}
		// Store intermediate results
		v = append(v, coef)
		u = u[i+1:]
	}
	// In this case, the encoding is invalid
	if len(v) != n {
		return nil, ErrInvalidEncoding
	}
	return v, nil
}
