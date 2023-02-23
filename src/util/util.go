package util

import (
	cryptoRand "crypto/rand"
	"encoding/binary"
	"encoding/hex"
	"math"
	"math/big"
)

//var NewBigInt = new(big.Int).Int.SetUint64(0)

//var NewBigFloat = types.NewBigFloat

const Q = 12289 //Q = 12*1024 + 1  (Q is the integer modulus which is used in Falcon.)

func UintFromBytes(b []byte) uint64 {
	data := binary.LittleEndian.Uint64(b)
	return data
}

// RandomBytes fills the given byte slice with random bytes.
func RandomBytes(data []byte) error {
	_, err := cryptoRand.Read(data)
	return err
}

func RandElement(elements []int) int {
	nBig, err := cryptoRand.Int(cryptoRand.Reader, big.NewInt(int64(len(elements))))
	if err != nil {
		panic(err)
	}
	n := nBig.Int64()
	return elements[n]
}

// RandomFft generates a random number in range [-3, 4]
func RandomFft() float64 {
	x := []int{-3, -2, -1, 0, 1, 2, 3, 4}
	elmnt := RandElement(x)
	return float64(elmnt)
}

// GenerateRandSalt generates a random salt of length SaltLen.
// each bit has a 50% chance of being 0 or 1.
func GenerateRandSalt() []byte {
	// TODO
	return nil
}

// RandomHexString generates a hex string with fixed length
func RandomHexString(length int) string {
	if length == 0 {
		return ""
	}
	b := make([]byte, length)
	_ = RandomBytes(b)
	s := hex.EncodeToString(b)
	return s
}

// Positive modulo, returns non negative solution to x % b
func Pmod(x, b int) int {
	x = x % b
	if x >= 0 {
		return x
	}
	if b < 0 {
		return x - b
	}
	return x + b
}

// Max takes variadic number of int's and returns the biggest one of them
func Max(a ...int) int {
	biggest := a[0]
	for _, v := range a {
		if v > biggest {
			biggest = v
		}
	}
	return biggest
}

// Min compares x and y and returns the smallest one of them
func Min(a float64, b float64) float64 {
	if a < b {
		return a
	}
	return b
}

func SmallestFloat64(f []float64) float64 {
	smallest := f[0]
	for _, v := range f {
		if v < smallest {
			smallest = v
		}
	}
	return smallest
}

func BiggestFloat64(f []float64) float64 {
	biggest := f[0]
	for _, v := range f {
		if v > biggest {
			biggest = v
		}
	}
	return biggest
}

func IntToInt16(s []int) []int16 {
	r := make([]int16, len(s))
	for i, v := range s {
		r[i] = int16(v)
	}
	return r
}

func ComplexRealToFloat64(c []complex128) []float64 {
	f := make([]float64, len(c))
	for i := 0; i < len(c); i++ {
		f[i] = real(c[i])
	}
	return f
}

func Float64ToComplexReal(f []float64) []complex128 {
	c := make([]complex128, len(f))
	for i := 0; i < len(f); i++ {
		c[i] = complex(f[i], 0)
	}
	return c
}

func Int8ToFloat64(f []int8) []float64 {
	n := len(f)
	r := make([]float64, n)
	for i := 0; i < n; i++ {
		r[i] = float64(f[i])
	}
	return r
}

func Int16ToFloat64(f []int16) []float64 {
	n := len(f)
	r := make([]float64, n)
	for i := 0; i < n; i++ {
		r[i] = float64(f[i])
	}
	return r
}

// func that will take int16 slice and return big.Int slice
func Int16ToBigInt(s []int16) []*big.Int {
	r := make([]*big.Int, len(s))
	FillBigIntSlice(r)
	for i, v := range s {
		r[i].SetInt64(int64(v))
	}
	return r
}

func SquareInt16(x int16) int16 {
	return x * x
}

func SubFloat64(x []float64, y []float64) []float64 {
	r := make([]float64, len(x))
	for i := 0; i < len(x); i++ {
		r[i] = x[i] - y[i]
	}
	return r
}

func SubInt16(x []int16, y []int16) []int16 {
	r := make([]int16, len(x))
	for i := 0; i < len(x); i++ {
		r[i] = x[i] - y[i]
	}
	return r
}

func NegFloat64(x []float64) []float64 {
	r := make([]float64, len(x))
	for i := 0; i < len(x); i++ {
		r[i] = -x[i]
	}
	return r
}

func NegInt16(x []int16) []int16 {
	r := make([]int16, len(x))
	for i := 0; i < len(x); i++ {
		r[i] = -x[i]
	}
	return r
}

func IntToBigInt(s []int) []*big.Int {
	r := make([]*big.Int, len(s))
	FillBigIntSlice(r)
	for i, v := range s {
		r[i].SetInt64(int64(v))
	}
	return r
}

func BigIntToInt16(x []*big.Int) []int16 {
	r := make([]int16, len(x))
	for i, v := range x {
		r[i] = int16(v.Int64())
	}
	return r
}

func Float64ToInt16(f []float64) []int16 {
	n := len(f)
	r := make([]int16, n)
	for i := 0; i < n; i++ {
		r[i] = int16(f[i])
	}
	return r
}

// func that fill a slice with bn.SetInt64(0)
func FillBigIntSlice(s []*big.Int) {
	for i := range s {
		s[i] = new(big.Int)
	}
}

// MinFromBigNum compares x and y and returns the smallest one of them
func CmpMinFromBigInt(x *big.Int, y *big.Int) *big.Int {
	r := x.Cmp(y)
	if r == -1 || r == 0 {
		return x
	}
	if r == 1 {
		return y
	}
	panic("")
}

// CmpBigInt compares x and y and returns true if both are equal
func CmpBigInt(x *big.Int, y *big.Int) bool {
	r := x.Cmp(y)
	return r == 0
}

// MaxFromBigNum compares x and y and returns the biggest one of them
func CmpMaxFromBigInt(x *big.Int, y *big.Int) *big.Int {
	r := x.Cmp(y)
	if r == 1 || r == 0 {
		return x
	}
	if r == -1 {
		return y
	}
	panic("")
}

// MaxFromBigNum returns the biggest one of them
func MaxFromBigInt(x []*big.Int) *big.Int {
	max := x[0]
	for _, v := range x {
		if v.Cmp(max) == 1 {
			max = v
		}
	}
	return max
}

// MinFromBigNum returns the smallest one of them
func MinFromBigInt(x []*big.Int) *big.Int {
	min := x[0]
	for _, v := range x {
		if v.Cmp(min) == -1 {
			min = v
		}
	}
	return min
}

// AllZeroes takes a slice of integers and returns true if all the elements of the slice are 0
func AllZeroes(numbers []int) bool {
	for _, n := range numbers {
		if n != 0 {
			return false
		}
	}
	return true
}

// BigIntSliceEqual returns true if the slices a and b have the same length and
// contain the same elements.
func BigIntSliceEqual(a, b []*big.Int) bool {
	if len(a) != len(b) {
		return false
	}
	for i, v := range a {
		if v.Cmp(b[i]) != 0 {
			return false
		}
	}
	return true
}

func AnyZeroes(numbers []int16) bool {
	for _, n := range numbers {
		if n == 0 {
			return true
		}
	}
	return false
}

func RoundAll(numbers []float64) []int {
	rounded := make([]int, len(numbers))
	for i, n := range numbers {
		rounded[i] = int(math.Round(n))
	}
	return rounded
}

// Split a polynomial f in two polynomials.
func SplitPolysInt(f []int16) ([]int16, []int16) {
	n := float64(len(f))         // create float from length of f
	fn := int(math.Floor(n / 2)) // floor returns the greatest integer value less than or equal to (n / 2)

	f0 := make([]int16, fn)
	f1 := make([]int16, fn)

	for i := 0; i < fn; i += 1 {
		a := 2 * i
		b := a + 1

		f0[i] = f[a]
		f1[i] = f[b]
	}

	return f0, f1
}

// Split a polynomial f in two polynomials.
func SplitPolysFloat64(f []float64) ([]float64, []float64) {
	n := float64(len(f))         // create float from length of f
	fn := int(math.Floor(n / 2)) // floor returns the greatest integer value less than or equal to (n / 2)

	f0 := make([]float64, fn)
	f1 := make([]float64, fn)

	for i := 0; i < fn; i += 1 {
		a := 2 * i
		b := a + 1

		f0[i] = f[a]
		f1[i] = f[b]
	}

	return f0, f1
}

// Merge two polynomials into a single polynomial f
func MergePolysInt(f0, f1 []int16) []int16 {

	n := 2 * len(f0)
	f := make([]int16, n)

	for i := 0; i < int(math.Floor(float64(n/2))); i += 1 {
		a := 2 * i
		b := a + 1

		f[a] = f0[i]
		f[b] = f1[i]
	}
	return f
}

// Merge two polynomials into a single polynomial f
func MergePolysfloat64(f0, f1 []float64) []float64 {

	n := 2 * len(f0)
	f := make([]float64, n)

	for i := 0; i < int(math.Floor(float64(n/2))); i += 1 {
		a := 2 * i
		b := a + 1

		f[a] = f0[i]
		f[b] = f1[i]
	}
	return f
}

// Sqnorm compute the square euclidean norm of the vector v.
func Sqnorm(v [][]float64) float64 {
	var res float64
	for _, elt := range v {
		for _, coef := range elt {
			res += math.Pow(float64(coef), 2)
		}
	}
	return res
}
