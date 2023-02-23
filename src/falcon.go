package falcon

import (
	"errors"
	"fmt"
	"math"

	"github.com/realForbis/go-falcon/src/internal"
	"github.com/realForbis/go-falcon/src/internal/transforms/fft"
	"github.com/realForbis/go-falcon/src/internal/transforms/ntt"
	"github.com/realForbis/go-falcon/src/util"

	_ "golang.org/x/crypto/chacha20"
	"golang.org/x/crypto/sha3"
)

//type (
//	Tree []any // LDL tree
//)

var (
	// ErrInvalidDegree is returned when the degree is not a power of 2
	ErrInvalidDegree = errors.New("n is not valid dimension/degree of the cyclotomic ring")
	// ErrInvalidPolysLenght is returned when the lenght of the polynomials is not equal to each other
	ErrInvalidPolysLength = errors.New("lenght of polynomials is not equal")
)

func isValidDegree(n uint16) bool {
	_, ok := ParamSets[n]
	return ok
}

func GetParamSet(n uint16) PublicParameters {
	if !isValidDegree(n) {
		return PublicParameters{}
	}
	return ParamSets[n]
}

func isValidPolysLength(n uint16, f, g, F, G []int16) bool {
	sum := uint16(len(f) + len(g) + len(F) + len(G))
	return sum%(4*n) == 0
}

func fft3D(polynomials [][][]float64) [][][]complex128 {
	fft3D := make([][][]complex128, len(polynomials))
	for i, row := range polynomials {
		fft3D[i] = make([][]complex128, len(row))
		for j, elt := range row {
			fft3D[i][j] = fft.FFT(elt)
		}
	}
	return fft3D
}

// From f, g, F, G, compute the basis B0 of a NTRU lattice
// as well as its Gram matrix and their fft's.
// return B0FFT, TFFT
func basisAndMatrix(f, g, F, G []int16) ([][][]complex128, internal.FFTtree) {
	B0 := [][][]float64{
		{util.Int16ToFloat64(g), fft.Neg(util.Int16ToFloat64(f))},
		{util.Int16ToFloat64(G), fft.Neg(util.Int16ToFloat64(F))},
	}
	G0 := internal.Gram(B0)
	B0FFT := fft3D(B0)
	G0FFT := fft3D(G0)
	TFFT := new(internal.FFTtree)
	TFFT.FfldlFFT(G0FFT)
	return B0FFT, *TFFT
}

// printTree prints a LDL tree in a human-readable format.
// Format: coefficient or fft
func printTree(tree []any, prefix string) string {
	leaf := "|_____> "
	top := "|_______"
	son1 := "|       "
	son2 := "        "
	width := len(top)
	var output string

	if len(tree) == 3 {
		if prefix == "" {
			output += prefix + fmt.Sprint(tree[0]) + "\n"
		} else {
			output += prefix[:len(prefix)-width] + top + fmt.Sprint(tree[0]) + "\n"
		}
		output += printTree(tree[1].([]any), prefix+son1)
		output += printTree(tree[2].([]any), prefix+son2)
		return output
	} else {
		return (prefix[:len(prefix)-width] + leaf + fmt.Sprint(tree) + "\n")
	}
}

func normalizeTree(tree [][]complex128, sigma float64) {
	fmt.Printf("\nnormalizeTree: sigma = %f, trees = %v", sigma, tree)
	if len(tree) == 3 {
		normalizeTree([][]complex128{tree[1], nil}, sigma)
		normalizeTree([][]complex128{tree[2], nil}, sigma)
	}
	tree[0][0] = complex(sigma/math.Sqrt(real(tree[0][0])), 0)
	tree[0][1] = 0

}

type PublicKey struct {
	n uint16
	h []int16
}

func NewPublicKey() *PublicKey {
	return new(PublicKey)
}

func (privKey *PrivateKey) GetPublicKey() *PublicKey {
	pubKey := NewPublicKey()
	pubKey.n = privKey.n
	// a polynomial such that h*f = g mod (Phi,q)
	pubKey.h, _ = ntt.DivZq(privKey.g, privKey.f)

	return pubKey
}

type Falcon struct {
	// ParamSet ParamSet
	PrivateKey
	B0FFT [][][]complex128
	TFFT  internal.FFTtree
	h     []int16
}

type PrivateKey struct {
	n uint16
	f []int16
	g []int16
	F []int16
	G []int16
}

// NewPrivateKey returns a new private key struct with empty fields.
func NewPrivateKey() *PrivateKey {
	return new(PrivateKey)
}

// GeneratePrivateKey generates a new private key.
func GeneratePrivateKey(n uint16) (*PrivateKey, error) {
	if !isValidDegree(n) {
		return nil, ErrInvalidDegree
	}
	privKey := NewPrivateKey()
	privKey.n = n
	// Compute NTRU polynomials f, g, F, G verifying fG - gF = q mod Phi
	privKey.f, privKey.g, privKey.F, privKey.G = internal.NtruGen(n)

	return privKey, nil
}

// GetPrivateKey returns a private key from the given polynomials.
func GetPrivateKey(n uint16, f, g, F, G []int16) (*PrivateKey, error) {
	if !isValidDegree(n) {
		return nil, ErrInvalidDegree
	}
	if !isValidPolysLength(n, f, g, F, G) {
		return nil, ErrInvalidPolysLength
	}
	privKey := NewPrivateKey()
	privKey.n = n
	privKey.f = f
	privKey.g = g
	privKey.F = F
	privKey.G = G

	return privKey, nil
}

// NewKeyPair generates a new keypair coresponding to the valid degree n.
func NewKeyPair(n uint16) (privKey *PrivateKey, pubKey *PublicKey, err error) {
	privKey, err = GeneratePrivateKey(n)
	if err != nil {
		return nil, nil, err
	}

	// Compute NTRU polynomials f, g, F, G verifying fG - gF = q mod Phi
	// falcon.PrivateKey.f, falcon.PrivateKey.g, falcon.PrivateKey.F, falcon.PrivateKey.G = internal.NtruGen(n)

	// falcon.B0FFT, falcon.TFFT = basisAndMatrix(
	// 	falcon.PrivateKey.f,
	// 	falcon.PrivateKey.g,
	// 	falcon.PrivateKey.F,
	// 	falcon.PrivateKey.G,
	// )
	// normalizeTree(falcon.TFFT.AllChild(), ParamSet.sigma)
	// falcon.h = ntt.Div_zq(falcon.PrivateKey.g, falcon.PrivateKey.f)
	return privKey, pubKey, nil
}

// func NewKeyPairFromPrivateKey(n uint16, polys [4][]int16) (privKey *PrivateKey, pubKey *PublicKey, err error) {
// 	falcon := new(Falcon)
// 	if !isValidDegree(n) {
// 		return nil, nil, ErrInvalidDegree
// 	}
// 	if !isValidPolysLength(n, polys) {
// 		return nil, nil, ErrInvalidPolysLength
// 	}

// 	falcon.PrivateKey.f = polys[0]
// 	falcon.PrivateKey.g = polys[1]
// 	falcon.PrivateKey.F = polys[2]
// 	falcon.PrivateKey.G = polys[3]

// 	falcon.B0FFT, falcon.TFFT = basisAndMatrix(
// 		falcon.PrivateKey.f,
// 		falcon.PrivateKey.g,
// 		falcon.PrivateKey.F,
// 		falcon.PrivateKey.G,
// 	)
// 	normalizeTree(falcon.TFFT.AllChild(), falcon.ParamSet.sigma)
// 	falcon.h = ntt.Div_zq(falcon.PrivateKey.g, falcon.PrivateKey.f)
// 	return privKey, pubKey, nil
// }

// Hash a message to a point in Z[x] mod(Phi, q).
// Inspired by the Parse function from NewHope.
func (privKey *PrivateKey) hashToPoint(message []byte, salt []byte) []float64 {
	if util.Q > (1 << 16) {
		panic("Q is too large")
	}

	k := (1 << 16) / util.Q
	// Create a SHAKE256 object and hash the salt and message
	shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)
	// Output pseudo-random bytes and map them to coefficients
	hashed := make([]float64, privKey.n)
	i := 0
	j := 0
	for i < int(privKey.n) {
		var buf [2]byte
		shake.Read(buf[:])
		// Map the bytes to coefficients
		elt := (int(buf[0]) << 8) + int(buf[1])
		// Implicit rejection sampling
		if elt < k*util.Q {
			hashed[i] = float64(elt % util.Q)
			i++
		}
		j++
	}
	return hashed
}

// Sample a short vector s such that s[0] + s[1] * h = point.
func (privKey *PrivateKey) samplePreImage(point []float64) [][]int16 {
	PubParam := GetParamSet(privKey.n)
	B0FFT, TFFT := basisAndMatrix(
		privKey.f,
		privKey.g,
		privKey.F,
		privKey.G,
	)
	a, b, c, d := B0FFT[0][0], B0FFT[0][1], B0FFT[1][0], B0FFT[1][1]
	var s [][]int16
	// We compute a vector t_fft such that:
	//     (fft(point), fft(0)) * B0_fft = t_fft
	// Because fft(0) = 0 and the inverse of B has a very specific form,
	// we can do several optimizations.
	pointFFT := fft.FFT(point)
	t0FFT := make([]complex128, privKey.n)
	t1FFT := make([]complex128, privKey.n)
	for i := 0; i < int(privKey.n); i++ {
		t0FFT[i] = (pointFFT[i] * d[i]) / util.Q
		t1FFT[i] = (-pointFFT[i] * b[i]) / util.Q
	}
	tFFT := [][]complex128{t0FFT, t1FFT}

	// We now compute v such that:
	//     v = z * B0 for an integral vector z
	//     v is close to (point, 0)
	zFFT := TFFT.FfSamplingFFT(tFFT, PubParam.sigmin)

	v0FFT := fft.AddFFT(fft.MulFFT(zFFT[0], a), fft.MulFFT(zFFT[1], c))
	v1FFT := fft.AddFFT(fft.MulFFT(zFFT[0], b), fft.MulFFT(zFFT[1], d))
	v0 := fft.RoundFFTtoInt16(v0FFT)
	v1 := fft.RoundFFTtoInt16(v1FFT)

	// The difference s = (point, 0) - v is such that:
	//     s is short
	//     s[0] + s[1] * h = point
	s[0] = util.SubInt16(util.Float64ToInt16(point), v0)
	s[1] = util.NegInt16(v1)
	return s
}

func (privKey *PrivateKey) Sign(message []byte) []byte {
	PubParam := GetParamSet(privKey.n)
	signature := []byte{byte(0x30 + LOGN[privKey.n])} // header
	var salt [SaltLen]byte
	util.RandomBytes(salt[:])
	hashed := privKey.hashToPoint(message, salt[:])

	// We repeat the signing procedure until we find a signature that is
	// short enough (both the Euclidean norm and the bytelength)
	for {
		var normSign uint32
		s := privKey.samplePreImage(hashed)

		for _, v := range s[0] {
			normSign += uint32(util.SquareInt16(v))
		}
		for _, v := range s[1] {
			normSign += uint32(util.SquareInt16(v))
		}
		if normSign <= PubParam.sigbound {
			encS, err := internal.Compress(s[1], int(PubParam.sigbytelen-HeadLen-SaltLen))
			if err != nil {
				continue
			}
			signature = append(signature, salt[:]...)
			signature = append(signature, encS...)
			return signature
		}
	}

}

/*
func (pk *PublicKey) String() string {
	return fmt.Sprintf("Public for n = %d:\nh = %d", pk.n, pk.h)
}

func (sk *SecretKey) HashToPoint(message []byte, salt []byte) []int {
	// code to hash the message
}



func (sk *SecretKey) Verify(message []byte, signature []byte) bool {
	// code to verify the signature
}

func (sk *SecretKey) String() string {
	return fmt.Sprintf("Private key for n = %d:\nf = %v\ng = %v\nF = %v\nG = %v", sk.n, sk.f, sk.g, sk.F, sk.G)
}
*/
