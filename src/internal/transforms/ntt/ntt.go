package ntt

import (
	"errors"
	"math"

	"github.com/realForbis/go-falcon/src/util"
)

//This file contains an implementation of the NTT.
//
//The NTT implemented here is for polynomials in Z_q[x]/(phi), with:
//- The integer modulus q = 12 * 1024 + 1 = 12289
//- The polynomial modulus phi = x ** n + 1, with n a power of two, n =< 1024
//
//The code is voluntarily very similar to the code of the FFT.
//It is probably possible to use templating to merge both implementations.

const i2 int16 = 6145          // i2 is the inverse of 2 mod q.
var sqr1 = roots_dict_Zq[2][0] // sqr1 is a square root of (-1) mod q (currently, sqr1 = 1479).

// This value is the ratio between:
//   - The degree n
//   - The number of complex coefficients of the NTT
//
// While here this ratio is 1, it is possible to develop a short NTT such that it is 2.
const NTTratio uint8 = 1

var (
	ErrDivByZero = errors.New("Division by zero")
)

// SplitNTT split a polynomial f in two or three polynomials
// fNTT: a polynomial
// Format: NTT
func SplitNTT(fNTT []int16) [][]int16 {
	n := len(fNTT)                            // lenght of fNTT
	floorN := int(math.Floor(float64(n) / 2)) // floor returns the greatest integer value less than or equal to (fn / 2)
	w := roots_dict_Zq[int16(n)]

	f0_NTT := make([]int16, floorN)
	f1_NTT := make([]int16, floorN)

	for i := 0; i < floorN; i += 1 {
		a := 2 * i
		b := a + 1

		// f0 refers to (i2 * (fNTT[2 * i] + fNTT[2 * i + 1])) % q
		f0 := int(fNTT[a]) + int(fNTT[b])
		f0 *= int(i2)
		f0 = util.Pmod(f0, int(util.Q))
		f0_NTT[i] = int16(f0)

		// f1 refers to (i2 * (fNTT[2 * i] - fNTT[2 * i + 1]) * inv_mod_q[w[2 * i]]) % q
		f1 := int(fNTT[a]) - int(fNTT[b])
		f1 *= int(i2)
		f1 *= int(inv_mod_q[w[a]])
		f1 = util.Pmod(f1, int(util.Q))
		f1_NTT[i] = int16(f1)
	}
	return [][]int16{f0_NTT, f1_NTT}
}

// MergeNTT merge two polynomials into a single polynomial f
// f_list_NTT: an array of polynomials
// Format: NTT
func MergeNTT(f_list_NTT [][]int16) []int16 {
	f0NTT, f1NTT := f_list_NTT[0], f_list_NTT[1]
	n := 2 * len(f0NTT)                       // lenght of fNTT
	floorN := int(math.Floor(float64(n) / 2)) // floor returns the greatest integer value less than or equal to (fn / 2)
	w := roots_dict_Zq[int16(n)]
	fNTT := make([]int16, n)

	for i := 0; i < floorN; i += 1 {
		a := 2 * i
		b := a + 1

		// f0 refers to (f0_NTT[i] + w[2 * i] * f1_NTT[i]) % q
		f0 := int(w[a]) * int(f1NTT[i])
		f0 += int(f0NTT[i])
		f0 = util.Pmod(f0, int(util.Q))
		fNTT[a] = int16(f0)

		// f1 refers to (f0_NTT[i] - w[2 * i] * f1_NTT[i]) % q
		f1 := int(w[a]) * int(f1NTT[i])
		f1 = int(f0NTT[i]) - f1
		f1 = util.Pmod(f1, int(util.Q))
		fNTT[b] = int16(f1)
	}
	return fNTT
}

// NTT compute the NTT of a polynomial
// f: a polynomial
// Format: input as coefficients, output as NTT
func NTT(f []int16) []int16 {
	var fNTT []int16
	n := len(f)
	if n > 2 {
		f0, f1 := util.SplitPolysInt(f)
		f0_NTT := NTT(f0)
		f1_NTT := NTT(f1)
		fNTT = MergeNTT([][]int16{f0_NTT, f1_NTT})
	} else if n == 2 {
		tmp := make([]int, n)
		a := int(sqr1) * int(f[1])

		// fNTT[0] refers to (f[0] + sqr1 * f[1]) % q
		x := int(f[0]) + a
		x = util.Pmod(x, int(util.Q))
		tmp[0] = x

		// fNTT[1] refers to (f[0] - sqr1 * f[1]) % q
		y := int(f[0]) - a
		y = util.Pmod(y, int(util.Q))
		tmp[1] = y

		fNTT = util.IntToInt16(tmp)
	}
	return fNTT
}

// INTT compute the inverse NTT of a polynomial.
// fNTT: a NTT of a polynomial
// Format: input as NTT, output as coefficients
func INTT(fNTT []int16) []int16 {
	var f []int16
	n := len(fNTT)
	if n > 2 {
		sNTT := SplitNTT(fNTT)
		f0 := INTT(sNTT[0])
		f1 := INTT(sNTT[1])
		f = util.MergePolysInt(f0, f1)
	} else if n == 2 {
		tmp := make([]int, 2)

		// x refers to (i2 * (fNTT[0] + fNTT[1])) % q
		x := int(fNTT[0]) + int(fNTT[1])
		x *= int(i2)
		x = util.Pmod(x, int(util.Q))
		tmp[0] = x

		// y refers to (i2 * inv_mod_q[1479] * (fNTT[0] - fNTT[1])) % q
		y := int(fNTT[0]) - int(fNTT[1])
		y *= int(inv_mod_q[1479])
		y *= int(i2)
		y = util.Pmod(y, int(util.Q))
		tmp[1] = y

		f = util.IntToInt16(tmp)
	}
	return f
}

// Addition of two polynomials (coefficient representation).
func addZq(f, g []int16) []int16 {
	res := make([]int16, len(f))
	if len(f) != len(g) {
		panic("lenght of f != lengh of g")
	}

	for i := range f {
		z := int(f[i] + g[i])
		z = util.Pmod(z, int(util.Q))
		res[i] = int16(z)
	}
	return res
}

// Negation of a polynomials (any representation).
func negZq(f []int16) []int16 {
	res := make([]int16, len(f))

	for i := range f {
		z := int(-(f[i]))
		z = util.Pmod(int(z), int(util.Q))
		res[i] = int16(z)
	}
	return res
}

// Substraction of two polynomials (any representation).
func subZq(f, g []int16) []int16 {
	g = negZq(g)
	return addZq(f, g)
}

// Multiplication of two polynomials (coefficient representation).
func MulZq(f, g []int16) []int16 {
	ft := NTT(f)
	gt := NTT(g)
	return INTT(mulNTT(ft, gt))
}

// Division of two polynomials (coefficient representation).
func DivZq(f, g []int16) ([]int16, error) {
	ft := NTT(f)
	gt := NTT(g)
	divNTT, err := divNTT(ft, gt)
	if err != nil {
		return nil, err
	}
	return INTT(divNTT), nil
}

// Addition of two polynomials (NTT representation).
func addNTT(fNTT, g_NTT []int16) []int16 {
	return addZq(fNTT, g_NTT)
}

// Substraction of two polynomials (NTT representation).
func subNTT(fNTT, g_NTT []int16) []int16 {
	return subZq(fNTT, g_NTT)
}

// Multiplication of two polynomials (coefficient representation).
func mulNTT(fNTT, g_NTT []int16) []int16 {
	res := make([]int16, len(fNTT))
	if len(fNTT) != len(g_NTT) {
		panic("lenght of fNTT != lengh of g_NTT")
	}

	for i := range fNTT {
		z := int(fNTT[i]) * int(g_NTT[i])
		z = util.Pmod(z, int(util.Q))
		res[i] = int16(z)
	}
	return res
}

// Division of two polynomials (NTT representation).
func divNTT(fNTT, g_NTT []int16) ([]int16, error) {
	if len(fNTT) != len(g_NTT) {
		panic("lenght of fNTT != lengh of g_NTT")
	}
	res := make([]int16, len(fNTT))
	for _, elt := range g_NTT {
		if elt == 0 {
			return nil, ErrDivByZero
		}
	}

	for i := range fNTT {
		z := int(fNTT[i]) * int(inv_mod_q[int(g_NTT[i])])
		z = util.Pmod(z, int(util.Q))
		res[i] = int16(z)
	}
	return res, nil
}
