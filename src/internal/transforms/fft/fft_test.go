package fft

import (
	"fmt"
	"math"
	"reflect"
	"testing"

	"github.com/realForbis/go-falcon/src/util"
)

func TestFft(t *testing.T) {
	for i := 6; i < 11; i++ {
		n := 1 << i
		t.Log("Test battery for n: ", n)

		f := make([]float64, n)
		g := make([]float64, n)
		for i := 0; i < n; i++ {
			f[i] = util.RandomFft()
			g[i] = util.RandomFft()
		}
		h := Mul(f, g)
		t.Log("h :", h)
		kInt := Div(h, f)
		k := make([]float64, len(kInt))
		for i, v := range kInt {
			k[i] = math.Round(v)
		}
		if !reflect.DeepEqual(k, g) {
			t.Error("(f * g) / f =", k)
			t.Error("g =", g)
			t.Fatal("mismatch")
		}
		t.Log("k == g")
	}
}

func BenchmarkFft(b *testing.B) {
	for i := 6; i < 11; i++ {
		n := 1 << i
		b.Run(fmt.Sprintf("n=%d", n), func(b *testing.B) {
			// Set up the input data
			f := make([]float64, n)
			g := make([]float64, n)
			for i := 0; i < n; i++ {
				f[i] = util.RandomFft()
				g[i] = util.RandomFft()
			}

			// Run the benchmark
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				h := Mul(f, g)
				kInt := Div(h, f)
				k := make([]float64, len(kInt))
				for i, v := range kInt {
					k[i] = math.Round(v)
				}
				if !reflect.DeepEqual(k, g) {
					b.Error("(f * g) / f =", k)
					b.Error("g =", g)
					b.Fatal("mismatch")
				}
			}
		})
	}
}

//func vecmatmult(t [][]float64, B [][][]float64) [][]float64 {
//	nrows := len(B)
//	ncols := len(B[0])
//	deg := len(B[0][0])
//
//	if len(t) != nrows {
//		panic("vecmatmult: invalid dimensions")
//	}
//
//	v := make([][]float64, ncols)
//	for i := 0; i < ncols; i++ {
//		v[i] = make([]float64, deg)
//	}
//
//	for j := 0; j < ncols; j++ {
//		for i := 0; i < nrows; i++ {
//			v[j] = add(v[j], mul(t[i], B[i][j]))
//		}
//	}
//	return v
//}

/*
func checkNtru(f, g, F, G []float64) bool {
	a := karamul(f, G)
	b := karamul(g, F)

	var c []float64
	for i := range f {
		c = append(c, a[i]-b[i])
	}

	var cf bool
	for _, v := range c[1:] {
		if v != 0 {
			cf = false
			break
		}
		cf = true
	}

	return c[0] == float64(util.Q) && cf
}
*/
