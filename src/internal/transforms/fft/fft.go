package fft

import (
	"math"
	"math/cmplx"

	"github.com/realForbis/go-falcon/src/util"
)

/*
This file contains an implementation of the FFT.

The FFT implemented here is for polynomials in R[x]/(phi), with:
- The polynomial modulus phi = x ** n + 1, with n a power of two, n =< 1024

The code is voluntarily very similar to the code of the FFT.
It is probably possible to use templating to merge both implementations.
*/

//This value is the ratio between:
//	- The degree n
//	- The number of complex coefficients of the NTT
//While here this ratio is 1, it is possible to develop a short NTT such that it is 2.

const FFTratio uint8 = 1

// SplitFft - Split a polynomial f in two polynomials
// f_fft: a polynomial
// format: FFT
// Corresponds to algorithm 1 (splitfft_2) of Falcon's documentation.
func SplitFFT(f_fft []complex128) [][]complex128 {
	n := len(f_fft)                           //length of f_fft
	floorN := int(math.Floor(float64(n) / 2)) // floor returns the greatest integer value less than or equal to (fn / 2)
	w := roots_dict[n]

	f0FFT := make([]complex128, floorN)
	f1FFT := make([]complex128, floorN)

	// f0 = f[2 * i] for i in range fn
	// f1 = f[2 * i + 1] for i in range fn
	for i := 0; i < floorN; i += 1 {
		a := 2 * i
		b := a + 1

		z := f_fft[a] + f_fft[b]
		z *= 0.5
		f0FFT[i] = z

		z = f_fft[a] - f_fft[b]
		z *= 0.5
		f1FFT[i] = z * cmplx.Conj(w[a])

	}
	return [][]complex128{f0FFT, f1FFT}
}

// Merge two or three polynomials into a single polynomial f.
// f_list: a list of polynomials
// format: FFT
// Corresponds to algorithm 2 (mergefft_2) of Falcon's documentation.
func MergeFFT(fl [][]complex128) []complex128 {
	f0_fft, f1_fft := fl[0], fl[1]
	n := 2 * len(f0_fft)
	floorN := int(math.Floor(float64(n) / 2)) // floor returns the greatest integer value less than or equal to (fn / 2)
	w := roots_dict[n]
	f_fft := make([]complex128, n)

	// f_fft[2 * i + 0] = f0_fft[i] + w[2 * i] * f1_fft[i]
	// f_fft[2 * i + 1] = f0_fft[i] - w[2 * i] * f1_fft[i]
	for i := 0; i < floorN; i += 1 {
		a := 2 * i
		b := a + 1
		cf0 := f0_fft[i] //complex(float64(f0_fft[i]), 0)
		cf1 := f1_fft[i] //complex(float64(f1_fft[i]), 0)

		z := w[a] * cf1
		z += cf0
		f_fft[a] = z

		z = w[a] * cf1
		z = cf0 - z
		f_fft[b] = z

	}

	return f_fft
}

// Compute the FFT of a polynomial mod (x ** n + 1).
// f: a polynomial
// Format: input as coefficients, output as FFT
func FFT(f []float64) []complex128 {
	var f_fft []complex128
	n := len(f)

	if n > 2 {
		f0, f1 := util.SplitPolysFloat64(f)
		f0_fft, f1_fft := FFT(f0), FFT(f1)
		f_fft = MergeFFT([][]complex128{f0_fft, f1_fft})
	} else if n == 2 {
		tmp := make([]complex128, 2)
		cf0 := complex(f[0], 0)
		cf1 := complex(f[1], 0)
		a := 1i * cf1

		// tmp[0] refers to f[0] + 1j * f[1]
		tmp[0] = cf0 + a

		// tmp[1] refers to f[0] - 1j * f[1]
		tmp[1] = cf0 - a

		f_fft = tmp
	}
	return f_fft
}

// Compute the inverse FFT of a polynomial mod (x ** n + 1).
// f: a FFT of a polynomial
// Format: input as FFT, output as coefficients
func IFFT(f_fft []complex128) []float64 {
	var f []float64
	n := len(f_fft)

	if n > 2 {
		fft := SplitFFT(f_fft)
		f0 := IFFT(fft[0])
		f1 := IFFT(fft[1])
		f = util.MergePolysfloat64(f0, f1)
	} else if n == 2 {
		tmp := make([]float64, n)

		tmp[0] = real(f_fft[0])
		tmp[1] = imag(f_fft[0])

		f = tmp
	}
	return f
}

// Addition of two polynomials (coefficient representation).
func Add(f, g []float64) []float64 {
	res := make([]float64, len(f))
	if len(f) != len(g) {
		panic("lenght of f != lengh of g")
	}

	for i := range f {
		z := f[i] + g[i]
		res[i] = z
	}
	return res
}

// Addition of two polynomials (FFT representation).
func AddFFT(f_fft, g_fft []complex128) []complex128 {
	res := make([]complex128, len(f_fft))
	if len(f_fft) != len(g_fft) {
		panic("lenght of f != lengh of g")
	}

	for i := range f_fft {
		z := f_fft[i] + g_fft[i]
		res[i] = z
	}
	return res
}

// Division of two polynomials (coefficient representation).
func Adj(f []float64) []float64 {
	return IFFT(AdjFFT(FFT(f)))
}

// Multiplication of two polynomials (coefficient representation).
func AdjFFT(f_fft []complex128) []complex128 {
	res := make([]complex128, len(f_fft))

	for i := range f_fft {
		res[i] = cmplx.Conj(f_fft[i])
	}
	return res
}

// Division of two polynomials (coefficient representation).
func Div(f, g []float64) []float64 {
	ft := FFT(f)
	gt := FFT(g)
	return IFFT(DivFFT(ft, gt))
}

// Division of two polynomials (FFT representation).
func DivFFT(f_fft, g_fft []complex128) []complex128 {
	res := make([]complex128, len(f_fft))
	if len(f_fft) != len(g_fft) {
		panic("lenght of f_fft != lengh of g_fft")
	}

	for i := range f_fft {
		z := f_fft[i] / g_fft[i]
		res[i] = z
	}
	return res
}

// Negation of a polynomials (any representation).
func Neg(f []float64) []float64 {
	res := make([]float64, len(f))

	for i := range f {
		z := -(f[i])
		res[i] = z
	}
	return res
}

func NegFFT(f []complex128) []complex128 {
	res := make([]complex128, len(f))

	for i := range f {
		z := -(f[i])
		res[i] = z
	}
	return res
}

// Multiplication of two polynomials (coefficient representation).
func Mul(f, g []float64) []float64 {
	ft := FFT(f)
	gt := FFT(g)
	return IFFT(MulFFT(ft, gt))
}

// Multiplication of two polynomials (coefficient representation).
func MulFFT(f_fft, g_fft []complex128) []complex128 {
	res := make([]complex128, len(f_fft))

	for i := range f_fft {
		z := f_fft[i] * g_fft[i]
		res[i] = z
	}
	return res
}

// Substraction of two polynomials (any representation).
func Sub(f, g []float64) []float64 {
	g = Neg(g)
	return Add(f, g)
}

// Substraction of two polynomials (FFT representation).
func SubFFT(f_fft, g_fft []complex128) []complex128 {
	g_fft = NegFFT(g_fft)
	return AddFFT(f_fft, g_fft)
}

func RoundFFTtoInt16(FFT []complex128) []int16 {
	res := make([]int16, len(FFT))

	for i := range FFT {
		res[i] = int16(real(FFT[i]))
	}
	return res
}
