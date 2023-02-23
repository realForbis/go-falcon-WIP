package types

/*
type BigFloat struct {
	big.Float
}

func NewBigFloatFromBigInt(x *big.Int) *BigFloat {
	bf := new(BigFloat)
	bf.Float.SetInt(x)
	return bf
}

func NewBigFloatFromBigNum(x *BigNum) *BigFloat {
	bf := new(BigFloat)
	bf.Float.SetInt(&x.Int)
	return bf
}

func NewBigFloatFromInt(x int64) *BigFloat {
	bf := new(BigFloat)
	bf.Float.SetInt64(x)
	return bf
}

func NewBigFloatFromFloat64(x float64) *BigFloat {
	bf := new(BigFloat)
	bf.Float.SetFloat64(x)
	return bf
}

func NewBigFloatFromString(x string) *BigFloat {
	bf := new(BigFloat)
	bf.Float.SetString(x)
	return bf
}

func (bf *BigFloat) Cmp(y *BigFloat) int {
	return bf.Float.Cmp(&y.Float)
}

func (bf *BigFloat) CmpBigFloat(y *big.Float) int {
	return bf.Float.Cmp(y)
}

func (bf *BigFloat) Add(x *BigFloat, y *BigFloat) *BigFloat {
	bf.Float.Add(&x.Float, &y.Float)
	return bf
}

func (bf *BigFloat) ToBigNum() (*big.Int, big.Accuracy) {
	z, a := bf.Float.Int(nil)
	return new(big.Int).I(z), a
}

func (bf *BigFloat) ToInt64() (int64, big.Accuracy) {
	z, a := bf.Float.Int64()
	return z, a
}

func (bf *BigFloat) AddBigFloat(x *big.Float, y *big.Float) *BigFloat {
	bf.Float.Add(x, y)
	return bf
}

func (bf *BigFloat) Sub(x *BigFloat, y *BigFloat) *BigFloat {
	bf.Float.Sub(&x.Float, &y.Float)
	return bf
}

func (bf *BigFloat) Mul(x *BigFloat, y *BigFloat) *BigFloat {
	bf.Float.Mul(&x.Float, &y.Float)
	return bf
}

func (bf *BigFloat) Quo(x *BigFloat, y *BigFloat) *BigFloat {
	bf.Float.Quo(&x.Float, &y.Float)
	return bf
}

func (bf *BigFloat) MulBigFloat(x *big.Float, y *big.Float) *BigFloat {
	bf.Float.Mul(x, y)
	return bf
}
*/
