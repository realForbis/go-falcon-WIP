package internal

import (
	"math"
	"math/big"

	"github.com/realForbis/go-falcon/src/types"
	"github.com/realForbis/go-falcon/src/util"
)

// Upper bound on all the values of sigma
const maxSigma float64 = 1.8205

var inv2sigma2 float64 = 1 / (2 * (math.Pow(maxSigma, 2)))

// Precision of RCDT
const RCDTprec uint8 = 72
const RCDTprecLen uint8 = (RCDTprec >> 3)

// ln(2) and 1 / ln(2), with ln the natural logarithm
var LN2 float64 = 0.69314718056
var ILN2 float64 = 1.44269504089

// RCDT is the reverse cumulative distribution table of a distribution that
// is very close to a half-Gaussian of parameter MAX_SIGMA.
var RCDT = [18]*big.Int{
	types.NewBigIntFromString("3024686241123004913666"),
	types.NewBigIntFromString("1564742784480091954050"),
	types.NewBigIntFromString("636254429462080897535"),
	types.NewBigIntFromString("199560484645026482916"),
	types.NewBigIntFromString("47667343854657281903"),
	types.NewBigIntFromString("8595902006365044063"),
	types.NewBigIntFromString("1163297957344668388"),
	types.NewBigIntFromString("117656387352093658"),
	types.NewBigIntFromString("8867391802663976"),
	types.NewBigIntFromString("496969357462633"),
	types.NewBigIntFromString("20680885154299"),
	types.NewBigIntFromString("638331848991"),
	types.NewBigIntFromString("14602316184"),
	types.NewBigIntFromString("247426747"),
	types.NewBigIntFromString("3104126"),
	types.NewBigIntFromString("28824"),
	types.NewBigIntFromString("198"),
	types.NewBigIntFromString("1"),
}

// C contains the coefficients of a polynomial that approximates exp(-x)
// More precisely, the value:
// (2 ** -63) * sum(C[12 - i] * (x ** i) for i in range(i))
// Should be very close to exp(-x).
// This polynomial is lifted from FACCT: https://doi.org/10.1109/TC.2019.2940949
var C = [13]uint64{
	0x00000004741183A3, // 19127174051
	0x00000036548CFC06, // 233346759686
	0x0000024FDCBF140A, // 2542029181962
	0x0000171D939DE045, // 25415798087749
	0x0000D00CF58F6F84, // 228754078003076
	0x000680681CF796E3, // 1830034511206115
	0x002D82D8305B0FEA, // 12810238987800554
	0x011111110E066FD0, // 76861433589428176
	0x0555555555070F00, // 384307168197152512
	0x155555555581FF00, // 1537228672812056320
	0x400000000002B400, // 4611686018427565056
	0x7FFFFFFFFFFF4800, // 9223372036854728704
	0x8000000000000000, // 9223372036854775808
}

// Require: -
// Ensure: An integer z0 ∈ {0, . . . , 18} such that z ∼ χ ▷ χ is uniquely defined by (3.33)
// 1: u ← UniformBits(72)
// 2: z0 ← 0
// 3: for i = 0, . . . , 17 do
// 4: z0 ← z0 + Ju < RCDT[i]K
// 5: return z0
// https://falcon-sign.info/falcon.pdf#57
func baseSampler(randomBytes [RCDTprecLen]byte) int {
	var z0 int
	u := new(big.Int).SetBytes(randomBytes[:])
	for _, elt := range RCDT {
		// z0 += 1 if (u < elt)
		if u.Cmp(elt) == -1 {
			z0 += 1
		}
	}
	return z0
}

// Require: Floating-point values x ∈ [0, ln(2)] and ccs ∈ [0, 1]
// Ensure: An integral approximation of 263 · ccs · exp(−x)
// 1: C = [0x00000004741183A3,0x00000036548CFC06,0x0000024FDCBF140A,0x0000171D939DE045,0x0000D00CF58F6F84, 0x000680681CF796E3, 0x002D82D8305B0FEA, 0x011111110E066FD0,0x0555555555070F00, 0x155555555581FF00, 0x400000000002B400, 0x7FFFFFFFFFFF4800,0x8000000000000000]
// 2: y ← C[0]
// 3: z ← ⌊263 · x⌋
// 4: for 1 = 1, . . . , 12 do
// 5: y ← C[u] − (z · y) >> 63
// 6: z ← ⌊263 · ccs⌋
// 7: y ← (z · y) >> 63
// 8: return y
// https://falcon-sign.info/falcon.pdf#d0
func approxexp(x, ccs float64) uint64 {
	y := C[0]
	// Since z is positive, int is equivalent to floor
	z := uint64(x * (1 << 63))
	for _, elt := range C[1:] {
		y = elt - ((z * y) >> 63)
	}
	z = uint64(ccs*float64(1<<63)) << 1
	y = (z * y) >> 63
	return y
}

// Require: Floating point values x, ccs ≥ 0
// Ensure: A single bit, equal to 1 with probability ≈ ccs · exp(−x)
// 1: s ← ⌊x/ ln(2)⌋
// 2: r ← x − s · ln(2)
// 3: s ← min(s, 63)
// 4: z ← (2 · ApproxExp(r, ccs) − 1) >> s ▷ z ≈ 264−s · ccs · exp(−r) = 264 · ccs · exp(−x)
// 5: i ← 64
// 6: do
// 7: i ← i − 8
// 8: w ← UniformBits(8) − ((z >> i) & 0xFF)
// 9: while ((w = 0) and (i > 0))
// 10: return Jw < 0K ▷ Return 1 with probability 2−64 · z ≈ ccs · exp(−x)
// https://falcon-sign.info/falcon.pdf#cf
func berexp(x, ccs float64, randomBytes []byte) bool {
	var w int
	s := math.Floor(x * ILN2)
	r := x - s*LN2
	s = util.Min(s, 63)
	z := (approxexp(r, ccs) - 1) >> int(s)
	for i := 56; i >= -8; i -= 8 {
		b := int(new(big.Int).SetBytes(randomBytes).Uint64())
		w = b - int((z>>uint64(i)))&0xFF
		if w != 0 {
			break
		}
	}
	return w < 0
}

// Given floating-point values mu, sigma (and sigmin),
// output an integer z according to the discrete
// Gaussian distribution D_{Z, mu, sigma}.
//
// Input:
// - the center mu
// - the standard deviation sigma
// - a scaling factor sigmin
// The inputs MUST verify 1 < sigmin < sigma < MAX_SIGMA.
//
// Output:
// - a sample z from the distribution D_{Z, mu, sigma}.
// https://falcon-sign.info/falcon.pdf#58
func Samplerz(mu, sigma, sigmin float64) int8 {
	s := int(math.Floor(mu))
	r := mu - float64(s)
	dss := 1 / (2 * sigma * sigma)
	ccs := sigmin / sigma
	var fb [9]byte
	var sb [1]byte
	var tb []byte
	for {
		fb, sb, tb = generateAndSplitRandBytes()
		z0 := baseSampler(fb)
		b := int(new(big.Int).SetBytes(sb[:]).Uint64())
		b &= 1
		z := float64(b + (2*b-1)*z0)
		x := math.Pow((z-r), 2) * dss
		x -= math.Pow(float64(z0), 2) * inv2sigma2
		if berexp(x, ccs, tb) {
			return int8(s + int(z))
		}
	}
}

func generateAndSplitRandBytes() ([9]byte, [1]byte, []byte) {
	rb, err := generateRandBytes()
	if err != nil {
		panic(err)
	}
	return splitRandBytes(rb)
}

func generateRandBytes() ([11]byte, error) {
	var rb [11]byte
	err := util.RandomBytes(rb[:])
	return rb, err
}

// splitRandBytes will split a byte slice (rb) into three byte slices
func splitRandBytes(randBytes [11]byte) ([9]byte, [1]byte, []byte) {
	var baseSamplerRandBytes [9]byte
	var samplerzRandBytes [1]byte
	var berexpSamplerRandBytes []byte

	copy(baseSamplerRandBytes[:], randBytes[:9])
	copy(samplerzRandBytes[:], randBytes[9:10])
	berexpSamplerRandBytes = randBytes[10:]

	return baseSamplerRandBytes, samplerzRandBytes, berexpSamplerRandBytes
}
