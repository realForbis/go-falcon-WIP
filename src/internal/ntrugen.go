package internal

import (
	"errors"
	"math"
	"math/big"

	"github.com/realForbis/go-falcon/src/internal/transforms/fft"
	"github.com/realForbis/go-falcon/src/internal/transforms/ntt"
	"github.com/realForbis/go-falcon/src/util"
)

/*
This file implements the section 3.8.2 of Falcon's documentation.
*/

var (
	ErrEquation = errors.New("NTRU equation has no solution")
)

// Karatsuba multiplication between polynomials.
// The coefficients may be either integer or real.
func Karatsuba(a, b []*big.Int, n int) []*big.Int {
	if n == 1 {
		// If n is 1, return the values of the two input numbers
		return []*big.Int{new(big.Int).Mul(a[0], b[0]), big.NewInt(0)}
	} else {
		// If n is not 1, split the input numbers into two halves
		n2 := n / 2
		a0 := a[:n2]
		a1 := a[n2:]
		b0 := b[:n2]
		b1 := b[n2:]

		// Calculate the sum of the two halves of each input
		ax := make([]*big.Int, n2)
		bx := make([]*big.Int, n2)
		util.FillBigIntSlice(ax)
		util.FillBigIntSlice(bx)
		for i := 0; i < n2; i++ {
			ax[i].Add(a0[i], a1[i])
			bx[i].Add(b0[i], b1[i])
		}

		// Recursively calculate the values of the two halves of each input
		a0b0 := Karatsuba(a0, b0, n2)
		a1b1 := Karatsuba(a1, b1, n2)
		axbx := Karatsuba(ax, bx, n2)
		// Correct the value of axbx by subtracting the other values
		for i := 0; i < n; i++ {
			axbx[i].Sub(axbx[i], new(big.Int).Add(a0b0[i], a1b1[i]))
		}
		ab := make([]*big.Int, 2*n)
		util.FillBigIntSlice(ab)
		for i := 0; i < n; i++ {
			ab[i].Add(ab[i], a0b0[i])
			ab[i+n].Add(ab[i+n], a1b1[i])
			ab[i+n2].Add(ab[i+n2], axbx[i])
		}
		return ab
	}
}

// Karatsuba multiplication, followed by reduction mod (x ** n + 1).
func karamul(a, b []*big.Int) []*big.Int {
	n := len(a)
	ab := Karatsuba(a, b, n)
	abr := make([]*big.Int, n)
	util.FillBigIntSlice(abr)
	// abr = [ab[i] - ab[i + n] for i in range(n)]
	for i := 0; i < n; i++ {
		abr[i].Sub(ab[i], ab[i+n])
	}
	return abr
}

// Galois conjugate of an element a in Q[x] / (x ** n + 1).
// Here, the Galois conjugate of a(x) is simply a(-x).
func galoisConjugate(a []*big.Int) []*big.Int {
	res := make([]*big.Int, len(a))
	util.FillBigIntSlice(res)

	for i, v := range res {
		exp := new(big.Int).Exp(big.NewInt(-1), big.NewInt(int64(i)), nil)
		v.Mul(exp, a[i])
	}
	return res
}

// Project an element a of Q[x] / (x ** n + 1) onto Q[x] / (x ** (n // 2) + 1).
// Only works if n is a power-of-two.
func fieldNorm(a []*big.Int) []*big.Int {
	n2 := int(math.Floor(float64(len(a)) / 2))
	ae := make([]*big.Int, n2)
	ao := make([]*big.Int, n2)
	util.FillBigIntSlice(ae)
	util.FillBigIntSlice(ao)

	for i := 0; i < n2; i++ {
		ae[i].Set(a[2*i])
		ao[i].Set(a[2*i+1])
	}

	aeSquared := karamul(ae, ae)
	aoSquared := karamul(ao, ao)
	res := aeSquared[:]
	for i := 0; i < (n2 - 1); i++ {
		res[i+1].Sub(res[i+1], aoSquared[i]) //res[i+1] -= aoSquared[i]
	}
	res[0].Add(res[0], aoSquared[n2-1]) //res[0] += aoSquared[n2-1]
	return res
}

// Lift an element a of Q[x] / (x ** (n // 2) + 1) up to Q[x] / (x ** n + 1).
// The lift of a(x) is simply a(x ** 2) seen as an element of Q[x] / (x ** n + 1).
func lift(a []*big.Int) []*big.Int {
	n := len(a)
	al := make([]*big.Int, 2*n)
	util.FillBigIntSlice(al)
	for i := 0; i < n; i++ {
		al[2*i] = a[i]
	}
	return al
}

// Compute the bitsize of an element of Z (not counting the sign).
// The bitsize is rounded to the next multiple of 8.
// This makes the function slightly imprecise, but faster to compute.
func bitsize(a *big.Int) int {
	val := new(big.Int).Abs(a)
	var res int
	for val.Sign() > 0 {
		res += 8
		val.Rsh(val, 8) //val >>= 8
	}
	return res
}

// Reduce (F, G) relatively to (f, g).
// This is done via Babai's reduction.
// (F, G) <-- (F, G) - k * (f, g), where k = round((F f* + G g*) / (f f* + g g*)).
// Corresponds to algorithm 7 (Reduce) of Falcon's documentation.
func reduce(f, g, F, G []*big.Int) ([]*big.Int, []*big.Int) {
	n := len(f)

	size := util.Max(
		53,
		bitsize(util.MinFromBigInt(f)),
		bitsize(util.MaxFromBigInt(f)),
		bitsize(util.MinFromBigInt(g)),
		bitsize(util.MaxFromBigInt(g)),
	)

	fAdj := make([]float64, n)
	for i, elt := range f {
		// fAdj = [elt >> (size - 53) for elt in f]
		fAdj[i] = float64(new(big.Int).Rsh(elt, uint(size-53)).Int64())
	}

	gAdj := make([]float64, len(g))
	for i, elt := range g {
		// gAdj = [elt >> (size - 53) for elt in g]
		gAdj[i] = float64(new(big.Int).Rsh(elt, uint(size-53)).Int64())
	}

	faFft := fft.FFT(fAdj)
	gaFft := fft.FFT(gAdj)

	for {
		SIZE := util.Max(
			53,
			bitsize(util.MinFromBigInt(F)),
			bitsize(util.MaxFromBigInt(F)),
			bitsize(util.MinFromBigInt(G)),
			bitsize(util.MaxFromBigInt(G)),
		)

		if SIZE < size {
			break
		}

		FAdj := make([]float64, len(F))
		for i, elt := range F {
			FAdj[i] = float64(new(big.Int).Rsh(elt, uint(SIZE-53)).Int64())
		}

		GAdj := make([]float64, len(G))
		for i, elt := range G {
			GAdj[i] = float64(new(big.Int).Rsh(elt, uint(SIZE-53)).Int64())
		}

		FaFft := fft.FFT(FAdj)
		GaFft := fft.FFT(GAdj)

		denFft := fft.AddFFT(
			fft.MulFFT(faFft, fft.AdjFFT(faFft)),
			fft.MulFFT(gaFft, fft.AdjFFT(gaFft)),
		)
		numFft := fft.AddFFT(
			fft.MulFFT(FaFft, fft.AdjFFT(faFft)),
			fft.MulFFT(GaFft, fft.AdjFFT(gaFft)),
		)

		kFft := fft.DivFFT(numFft, denFft)
		k := util.RoundAll(fft.IFFT(kFft))

		if util.AllZeroes(k) {
			break
		}

		fk := karamul(f, util.IntToBigInt(k))
		gk := karamul(g, util.IntToBigInt(k))

		for i := 0; i < n; i++ {
			F[i].Sub(F[i], new(big.Int).Lsh(fk[i], uint(SIZE-size)))
			//F[i].Sub(F[i], fk[i])           //F[i] -= fk[i]
			//F[i].Lsh(F[i], uint(SIZE-size)) //F[i] <<= SIZE - size
			G[i].Sub(G[i], new(big.Int).Lsh(gk[i], uint(SIZE-size)))
			//G[i].Sub(G[i], gk[i])           //G[i] -= gk[i]
			//G[i].Lsh(G[i], uint(SIZE-size)) //G[i] <<= SIZE - size
		}
	}
	return F, G
}

// Compute the extended GCD of two integers(big.num's) b and n.
// Return d, u, v such that d = u * b + v * n, and d is the GCD of b, n.
func xgcd(b, n *big.Int) (*big.Int, *big.Int, *big.Int) {
	x0 := big.NewInt(1)
	x1 := big.NewInt(0)
	y0 := big.NewInt(0)
	y1 := big.NewInt(1)

	for n.Cmp(big.NewInt(0)) != 0 {
		q := big.NewInt(0)
		q.Div(b, n)
		b, n = n, big.NewInt(0).Mod(b, n)
		x0, x1 = x1, big.NewInt(0).Sub(x0, big.NewInt(0).Mul(q, x1))
		y0, y1 = y1, big.NewInt(0).Sub(y0, big.NewInt(0).Mul(q, y1))
	}
	return b, x0, y0
}

// Solve the NTRU equation for f and g.
// Corresponds to NTRUSolve in Falcon's documentation.
func NtruSolve(f, g []*big.Int) ([]*big.Int, []*big.Int, error) {
	n := len(f)
	if n == 1 {
		f0 := new(big.Int).Set(f[0])
		g0 := new(big.Int).Set(g[0])
		d, u, v := xgcd(f0, g0)

		if d.Int64() != 1 {
			return nil, nil, ErrEquation
		}
		q := big.NewInt(int64(util.Q))
		negQ := new(big.Int).Neg(q)

		// [- q * v], [q * u]
		return []*big.Int{new(big.Int).Mul(negQ, v)}, []*big.Int{new(big.Int).Mul(q, u)}, nil
	}
	fp := fieldNorm(f)
	gp := fieldNorm(g)
	Fp, Gp, err := NtruSolve(fp, gp)
	if err != nil {
		return nil, nil, ErrEquation
	}

	F := karamul(lift(Fp), galoisConjugate(g))
	G := karamul(lift(Gp), galoisConjugate(f))
	F, G = reduce(f, g, F, G)
	return F, G, nil

}

func GsNorm(f, g []float64, q float64) float64 {
	sqnormFg := util.Sqnorm([][]float64{f, g})
	ffgg := fft.Add(fft.Mul(f, fft.Adj(f)), fft.Mul(g, fft.Adj(g)))
	Ft := fft.Div(fft.Adj(f), ffgg)
	Gt := fft.Div(fft.Adj(g), ffgg)
	sqnormFG := math.Pow(q, 2) * util.Sqnorm([][]float64{Ft, Gt})
	return util.BiggestFloat64([]float64{sqnormFg, sqnormFG})
}

func GenPoly(n uint16) []int16 {
	sigma := 1.43300980528773 //1.17 * sqrt(12289 / 8192)
	if n > 4096 {
		panic("n < 4096")
	}
	var f0 []int8
	for i := 0; i < 4096; i++ {
		f0 = append(f0, Samplerz(0, sigma, (sigma-0.001)))
	}
	f := make([]int16, n)
	k := int(math.Floor(4096 / float64(n)))

	// f[i] = sum(f0[i * k + j] for j in range(k))
	var sum int
	for i := 0; i < int(n); i++ {
		sum = 0
		for j := 0; j < k; j++ {
			sum += int(f0[i*k+j])
		}
		f[i] = int16(sum)
	}
	return f
}

func NtruGen(n uint16) (f, g, F, G []int16) {
	for {
		f := GenPoly(n)
		g := GenPoly(n)

		if GsNorm(util.Int16ToFloat64(f), util.Int16ToFloat64(g), float64(util.Q)) > (math.Pow(1.17, 2) * float64(util.Q)) {
			continue
		}
		fntt := ntt.NTT(f)
		if util.AnyZeroes(fntt) {
			continue
		}

		BigF, BigG, err := NtruSolve(util.Int16ToBigInt(f), util.Int16ToBigInt(g))
		if err == ErrEquation {
			continue
		}

		F := util.BigIntToInt16(BigF)
		G := util.BigIntToInt16(BigG)
		return f, g, F, G
	}
}
