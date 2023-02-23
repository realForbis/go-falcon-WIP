package internal

import (
	"log"
	"math"

	"github.com/realForbis/go-falcon/src/internal/transforms/fft"
	"github.com/realForbis/go-falcon/src/util"
)

/*
This value is the ratio between:
  - The degree n
  - The number of complex coefficients of the NTT

While here this ratio is 1, it is possible to develop a short NTT such that it is 2.
*/
const fftRatio = 1

type FFTtree struct {
	Value      []complex128
	Leftchild  []complex128
	Rightchild []complex128
}

func (t *FFTtree) AllChild() [][]complex128 {
	return [][]complex128{t.Leftchild, t.Rightchild}
}

type CoeffTree struct {
}

func Gram(B [][][]float64) [][][]float64 {
	rows := len(B)
	ncols := len(B[0])
	deg := len(B[0][0])
	G := make([][][]float64, rows)
	for i := 0; i < rows; i++ {
		G[i] = make([][]float64, rows)
		for j := 0; j < rows; j++ {
			G[i][j] = make([]float64, deg)
		}
	}

	for i := 0; i < rows; i++ {
		for j := 0; j < rows; j++ {
			for k := 0; k < ncols; k++ {
				G[i][j] = fft.Add(G[i][j], fft.Mul(B[i][k], fft.Adj(B[j][k])))
			}
		}
	}

	return G
}

/*
// Compute the LDL decomposition of G. Only works with 2 * 2 matrixes.
// Format: coefficient
func Ldl(G [][][]float64) [][][][]float64 {
	deg := len(G[0][0])
	dim := len(G)
	if dim != 2 || dim != len(G[0]) {
		panic("G must be a 2 * 2 matrix")
	}

	// Initialize the zero and one polynomials
	zero := make([]float64, deg)
	one := append([]float64{1}, make([]float64, deg-1)...)

	// Compute the entries of the L and D matrices
	D00 := G[0][0][:]
	L10 := fft.Div(G[1][0], G[0][0])
	D11 := fft.Sub(G[1][1], fft.Mul(fft.Mul(L10, fft.Adj(L10)), G[0][0]))
	L := [][][]float64{{one, zero}, {L10, one}}
	D := [][][]float64{{D00, zero}, {zero, D11}}
	return [][][][]float64{L, D}
}
*/

func LdlFFT(G [][][]complex128) [][][][]complex128 {
	// Compute the LDL decomposition of G. Only works with 2 * 2 matrixes.
	// Format: FFT
	deg := len(G[0][0])
	dim := len(G)
	if dim != 2 || dim != len(G[0]) {
		panic("G must be a 2 * 2 matrix")
	}

	// Initialize the zero and one polynomials
	zero := make([]complex128, deg)
	one := make([]complex128, deg)
	for i := range one {
		one[i] = 1
	}

	// Compute the entries of the L and D matrices
	D00 := G[0][0][:]
	L10 := fft.DivFFT(G[1][0], G[0][0])
	D11 := fft.SubFFT(G[1][1], fft.MulFFT(fft.MulFFT(L10, fft.AdjFFT(L10)), G[0][0]))
	L := [][][]complex128{{one, zero}, {L10, one}}
	D := [][][]complex128{{D00, zero}, {zero, D11}}
	return [][][][]complex128{L, D}
}

/*
func Ffldl(G [][][]float64) [][]float64 {
	n := len(G[0][0])
	LD := Ldl(G)
	L, D := LD[0], LD[1]

	if n != 2 {
		panic("n must be 2")
	}
	// Coefficients of L, D are elements of R[x]/(x^n - x^(n/2) + 1), in coefficient representation
	//if n > 2 {
	//	// A bisection is done on elements of a 2*2 diagonal matrix.
	//	d00, d01 := util.SplitPolysFloat64(D[0][0])
	//	d10, d11 := util.SplitPolysFloat64(D[1][1])
	//	G0 := [][][]float64{{d00, d01}, {fft.Adj(d01), d00}}
	//	G1 := [][][]float64{{d10, d11}, {fft.Adj(d11), d10}}
	//	return [][]float64{L[1][0], Ffldl(G0), Ffldl(G1)}
	//} else if n == 2 {
	//	D[0][0][1] = 0
	//	D[1][1][1] = 0
	//	return [][]float64{L[1][0], D[0][0], D[1][1]}
	//}
	D[0][0][1] = 0
	D[1][1][1] = 0
	return [][]float64{L[1][0], D[0][0], D[1][1]}
}
*/

func (T *FFTtree) FfldlFFT(G [][][]complex128) FFTtree {
	n := len(G[0][0]) * fftRatio
	//log.Println("n :", n)
	LD := LdlFFT(G)
	L, D := LD[0], LD[1]
	T.Value = L[1][0]

	if n == 2 {
		T.Leftchild = D[0][0]
		T.Rightchild = D[1][1]
		log.Println("T: ", T)
		return *T
	}
	d0001 := fft.SplitFFT(D[0][0])
	d1011 := fft.SplitFFT(D[1][1])
	d00, d01 := d0001[0], d0001[1]
	d10, d11 := d1011[0], d1011[1]
	G0 := [][][]complex128{{d00, d01}, {fft.AdjFFT(d01), d00}}
	G1 := [][][]complex128{{d10, d11}, {fft.AdjFFT(d11), d10}}
	(*T).FfldlFFT(G0)
	(*T).FfldlFFT(G1)
	log.Println("T: ", T)
	return *T
}

/*
	n := len(G[0][0]) * fftRatio
	LD := LdlFft(G)
	L, D := LD[0], LD[1]

	if n > 2 {
		d0001 := fft.SplitFFT(D[0][0])
		d00, d01 := d0001[0], d0001[1]
		d1011 := fft.SplitFFT(D[1][1])
		d10, d11 := d1011[0], d1011[1]
		G0 := [][][]complex128{{d00, d01}, {fft.AdjFFT(d01), d00}}
		G1 := [][][]complex128{{d10, d11}, {fft.AdjFFT(d11), d10}}

		return [][]complex128{L[1][0], FfldlFFT(G0)[0], FfldlFFT(G1)[0]}
	} else if n == 2 {
		return [][]complex128{L[1][0], D[0][0], D[1][1]}
	}
	return nil
}
*/

/*
func Ffnp(t [][]float64, T []interface{}) [][]float64 {
	n := len(t[0])
	z := [][]float64{nil, nil}
	if n > 1 {
		l10, T0, T1 := T[0].([]float64), T[1].([]interface{}), T[2].([]interface{})
		x, y := util.SplitPolysFloat64(t[1])
		xy := [][]float64{x, y}
		t01 := Ffnp(xy, T1)
		t0, t1 := t01[0], t01[1]
		z[1] = util.MergePolysfloat64(t0, t1)
		t0b := fft.Add(t[0], fft.Mul(fft.Sub(t[1], z[1]), l10))
		x, y = util.SplitPolysFloat64(t0b)
		xy = [][]float64{x, y}
		t01 = Ffnp(xy, T0)
		t0, t1 = t01[0], t01[1]
		z[0] = util.MergePolysfloat64(t0, t1)
		return z
	} else if n == 1 {
		z[0] = []float64{math.Round(t[0][0])}
		z[1] = []float64{math.Round(t[1][0])}
		return z
	}
	return [][]float64{}
}
*/

func FfnpFFT(t [][]complex128, T []interface{}) [][]complex128 {
	n := len(t[0]) * fftRatio
	log.Println("n :", n)
	z := [][]complex128{{0}, {0}}
	if n > 1 {
		l10, T0, T1 := T[0].([]complex128), T[1].([]interface{}), T[2].([]interface{})
		t01 := FfnpFFT(fft.SplitFFT(t[1]), T1)
		z[1] = fft.MergeFFT(t01)
		t0b := fft.AddFFT(t[0], fft.MulFFT(fft.SubFFT(t[1], z[1]), l10))
		z[0] = fft.MergeFFT(FfnpFFT(fft.SplitFFT(t0b), T0))
		return z
	} else if n == 1 {
		z[0] = []complex128{complex(math.Round(real(t[0][0])), 0)}
		z[1] = []complex128{complex(math.Round(real(t[1][0])), 0)}
		return z
	}
	return nil
}

// Require: t = (t0, t1) ∈ FFT (Q[x]/(xn + 1))2, a Falcon tree T
// Ensure: z = (z0, z1) ∈ FFT (Z[x]/(xn + 1))2
// Format: All polynomials are in FFT representation.
// 1: if n = 1 then
// 2: 	σ′ ← T.value
// 3: 	z0 ← SamplerZ(t0, σ′)
// 4: 	z1 ← SamplerZ(t1, σ′)
// 5: 	return z = (z0, z1)
// 6: (ℓ, T0, T1) ← (T.value, T.leftchild, T.rightchild)
// 7: t1 ← splitfft(t1)
// 8: z1 ← ffSampling n/2(t1, T1)
// 9: z1 ← mergefft(z1)
// 10: t′0 ← t0 + (t1 − z1) ⊙ ℓ
// 11: t0 ← splitfft(t′0)
// 12: z0 ← ffSampling n/2(t0, T0)
// 13: z0 ← mergefft(z0)
// 14: return z = (z0, z1)
func (T *FFTtree) FfSamplingFFT(t [][]complex128, sigmin float64) [][]complex128 {
	n := len(t[0]) * fftRatio
	z := [][]complex128{{0 + 0i}, {0 + 0i}}
	var rb [9]byte
	util.RandomBytes(rb[:])
	if n > 1 {
		z[1] = fft.MergeFFT((*T).FfSamplingFFT(fft.SplitFFT(t[1]), sigmin))
		t0b := fft.AddFFT(t[0], fft.MulFFT(fft.SubFFT(t[1], z[1]), T.Value))
		z[0] = fft.MergeFFT((*T).FfSamplingFFT(fft.SplitFFT(t0b), sigmin))
		log.Println("z", z)
		return z
	} else if n == 1 {
		log.Println("real(t[0][0])", real(t[0][0]))
		if T.Leftchild[:] == nil {
			T.Leftchild = T.Rightchild
		}
		z[0] = []complex128{complex(float64(Samplerz(real(t[0][0]), real(T.Leftchild[0]), sigmin)), 0)}
		z[1] = []complex128{complex(float64(Samplerz(real(t[1][0]), real(T.Leftchild[0]), sigmin)), 0)}
		log.Println("z", z)
		return z
	}
	return z
}
