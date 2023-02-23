package types

import "math/big"

var NewBigInt = big.NewInt(0)
var NewBigFloat = big.NewFloat(0)

// base is set to 0
func NewBigIntFromString(s string) *big.Int {
	bn := new(big.Int)
	bn.SetString(s, 0)
	return bn
}

/*
func NewBigNumFromInt(x int64) *BigNum {
	bn := new(BigNum)
	bn.Int.SetInt64(x)
	return bn
}

func NewBigNumFromUint(x uint64) *BigNum {
	bn := new(BigNum)
	bn.Int.SetUint64(x)
	return bn
}

func NewBigNumFromBigInt(int *big.Int) *BigNum {
	bn := new(BigNum)
	bn.Int.SetBytes(int.Bytes())
	return bn
}



func NewBigNumFromBytes(b []byte) *BigNum {
	bn := new(BigNum)
	bn.Int.SetBytes(b)
	return bn
}

func (bn *BigNum) ToBigInt() *big.Int {
	return new(big.Int).SetBytes(bn.Int.Bytes())
}

func (bn *BigNum) Abs(x *BigNum) *BigNum {
	bn.Int.Abs(&x.Int)
	return bn
}

func (bn *BigNum) And(x, y *BigNum) *big.Int {
	return bn.Int.And(&x.Int, &y.Int)
}

func (bn *BigNum) Cmp(y *BigNum) int {
	return bn.Int.Cmp(&y.Int)
}

func (bn *BigNum) Add(x *BigNum, y *BigNum) *BigNum {
	bn.Int.Add(&x.Int, &y.Int)
	return bn
}

func (bn *BigNum) AddBigInt(x *big.Int, y *big.Int) *BigNum {
	bn.Int.Add(x, y)
	return bn
}

func (bn *BigNum) Sub(x *BigNum, y *BigNum) *BigNum {
	bn.Int.Sub(&x.Int, &y.Int)
	return bn
}

func (bn *BigNum) Mod(x, y *BigNum) *BigNum {
	bn.Int.Mod(&x.Int, &y.Int)
	return bn
}

func (bn *BigNum) Sign() int {
	return bn.Int.Sign()
}

func (bn *BigNum) SubBigInt(x *big.Int, y *big.Int) *BigNum {
	bn.Int.Sub(x, y)
	return bn
}

func (bn *BigNum) Div(x *BigNum, y *BigNum) *BigNum {
	bn.Int.Div(&x.Int, &y.Int)
	return bn
}

func (bn *BigNum) DivBigInt(x *big.Int, y *big.Int) *BigNum {
	bn.Int.Div(x, y)
	return bn
}

func (bn *BigNum) Mul(x *BigNum, y *BigNum) *BigNum {
	bn.Int.Mul(&x.Int, &y.Int)
	return bn
}

func (bn *BigNum) Neg() *BigNum {
	bn.Int.Neg(&bn.Int)
	return bn
}

func (bn *BigNum) Rsh(x *BigNum, n uint) *BigNum {
	bn.Int.Rsh(&x.Int, n)
	return bn
}

func (bn *BigNum) Lsh(x *BigNum, n uint) *BigNum {
	bn.Int.Lsh(&x.Int, n)
	return bn
}

func (bn *BigNum) Exp(x, y *BigNum) *BigNum {
	bn.Int.Exp(&x.Int, &y.Int, nil)
	return bn
}

func (bn *BigNum) IsUint64() bool {
	return bn.Int.IsUint64()
}

func (bn *BigNum) IsInt64() bool {
	return bn.Int.IsInt64()
}

func (bn *BigNum) Int64() int64 {
	return bn.Int.Int64()
}

func (bn *BigNum) MulBigInt(x *big.Int, y *big.Int) *BigNum {
	bn.Int.Mul(x, y)
	return bn
}

func (bn *BigNum) Copy() *BigNum {
	copyBN := new(BigNum)
	copyBN.Int.SetBytes(bn.Int.Bytes())
	return copyBN
}

//ExtensionType implements Extension.Len interface
func (bn *BigNum) Len() int { return len(bn.Int.Bytes()) }

//ExtensionType implements Extension.UnmarshalBinary interface
func (bn *BigNum) MarshalBinaryTo(text []byte) error {
	copy(text, bn.Int.Bytes())
	return nil
}

//ExtensionType implements Extension.UnmarshalBinary interface
func (bn *BigNum) UnmarshalBinary(text []byte) error {
	bn.Int.SetBytes(text)
	return nil
}
*/
