package internal

import "testing"

/*
import (
	"encoding/hex"
	"testing"
)

func decodeHexString(hexString string) []byte {
	byteSlice, err := hex.DecodeString(hexString)
	if err != nil {
		panic(err)
	}
	return byteSlice
}

func TestBaseSampler(t *testing.T) {
	// Test that baseSampler returns a value in the expected range.
	z0 := baseSampler()
	if z0 < 0 || z0 > 18 {
		t.Errorf("baseSampler returned a value outside the expected range: got %d, want [0, 18]", z0)
	}
}


func TestSamplerZ(t *testing.T) {
	type vectors struct {
		center            float64
		standardDeviation float64
		randombytes       []byte
		Output            int
	}
	// Test vectors for SamplerZ
	// https://falcon-sign.info/falcon.pdf#59
	testVectors := map[uint8]vectors{
		1: {
			center:            -91.90471153063714,
			standardDeviation: 1.7037990414754918,
			randombytes:       decodeHexString("0fc5442ff043d66e91d1eacac64ea5450a22941edc6c"),
			Output:            -92,
		},
		2: {
			center:            -8.322564895434937,
			standardDeviation: 1.7037990414754918,
			randombytes:       decodeHexString("f4da0f8d8444d1a77265c2ef6f98bbbb4bee7db8d9b3"),
			Output:            -8,
		},
		3: {
			center:            -19.096516109216804,
			standardDeviation: 1.7035823083824078,
			randombytes:       decodeHexString("db47f6d7fb9b19f25c36d6b9334d477a8bc0be68145d"),
			Output:            -20,
		},
		4: {
			center:            -11.335543982423326,
			standardDeviation: 1.7035823083824078,
			randombytes:       decodeHexString("ae41b4f5209665c74d00dcc1a8168a7bb516b3190cb42c1ded26cd52aed770eca7dd334e0547bcc3c163ce0b"),
			Output:            -12,
		},
		5: {
			center:            7.9386734193997555,
			standardDeviation: 1.6984647769450156,
			randombytes:       decodeHexString("31054166c1012780c603ae9b833cec73f2f41ca5807cc89c92158834632f9b1555"),
			Output:            8,
		},
		6: {
			center:            -28.990850086867255,
			standardDeviation: 1.6984647769450156,
			randombytes:       decodeHexString("737e9d68a50a06dbbc6477"),
			Output:            -30,
		},
		7: {
			center:            -9.071257914091655,
			standardDeviation: 1.6980782114808988,
			randombytes:       decodeHexString("a98ddd14bf0bf22061d632"),
			Output:            -10,
		},
		8: {
			center:            -43.88754568839566,
			standardDeviation: 1.6980782114808988,
			randombytes:       decodeHexString("3cbf6818a68f7ab9991514"),
			Output:            -41,
		},
		9: {
			center:            -58.17435547946095,
			standardDeviation: 1.7010983419195522,
			randombytes:       decodeHexString("6f8633f5bfa5d26848668e3d5ddd46958e97630410587c"),
			Output:            -61,
		},
		10: {
			center:            -43.58664906684732,
			standardDeviation: 1.7010983419195522,
			randombytes:       decodeHexString("272bc6c25f5c5ee53f83c43a361fbc7cc91dc783e20a"),
			Output:            -46,
		},
		11: {
			center:            -34.70565203313315,
			standardDeviation: 1.7009387219711465,
			randombytes:       decodeHexString("45443c59574c2c3b07e2e1d9071e6d133dbe32754b0a"),
			Output:            -34,
		},
		12: {
			center:            -44.36009577368896,
			standardDeviation: 1.7009387219711465,
			randombytes:       decodeHexString("6ac116ed60c258e2cbaeab728c4823e6da36e18d08da5d0cc104e21cc7fd1f5ca8d9dbb675266c928448059e"),
			Output:            -44,
		},
		13: {
			center:            -21.783037079346236,
			standardDeviation: 1.6958406126012802,
			randombytes:       decodeHexString("68163bc1e2cbf3e18e7426"),
			Output:            -23,
		},
		14: {
			center:            -39.68827784633828,
			standardDeviation: 1.6958406126012802,
			randombytes:       decodeHexString("d6a1b51d76222a705a0259"),
			Output:            -40,
		},
		15: {
			center:            -18.488607061056847,
			standardDeviation: 1.6955259305261838,
			randombytes:       decodeHexString("f0523bfaa8a394bf4ea5c10f842366fde286d6a30803"),
			Output:            -22,
		},
		16: {
			center:            -48.39610939101591,
			standardDeviation: 1.6955259305261838,
			randombytes:       decodeHexString("87bd87e63374cee62127fc6931104aab64f136a0485b"),
			Output:            -50,
		},
	}
	sigmin := 1.277833697
}
*/

func TestSamplerz(t *testing.T) {
	sigma := 1.43300980528773
	sigmin := sigma - 0.001
	out := Samplerz(0, sigma, sigmin)
	t.Log(out)
}
