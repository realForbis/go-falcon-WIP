package falcon

// Bytelength of the signing salt and header
const HeadLen = 4
const SaltLen = 40 // {0, 1}^320
const SeedLen = 56

//the degree is provided logarithmically as the 'LOGN' parameter: LOGN ranges from 1 to 10, and represents the degree 2^LOGN.
//use :
//	  LOGN=9 for Falcon-512
//	  LOGN=10 for Falcon-1024
//Valid values for LOGN range from 1 to 10
//(values 1 to 8 correspond to reduced variants of Falcon that do not
//provided adequate security and are meant for research purposes only).
//
//The sizes are provided as macros that evaluate to constant
//expressions, as long as the 'LOGN' parameter is itself a constant
//expression. Moreover, all sizes are monotonic (for each size category,
//increasing LOGN cannot result in a shorter length).
var LOGN = map[uint16]uint8{
	2:    1,
	4:    2,
	8:    3,
	16:   4,
	32:   5,
	64:   6,
	128:  7,
	256:  8,
	512:  9,
	1024: 10,
}

// Parameter sets for Falcon:
// - n is the dimension/degree of the cyclotomic ring
// - sigma is the std. dev. of signatures (Gaussians over a lattice)
// - sigmin is a lower bounds on the std. dev. of each Gaussian over Z
// - sigbound is the upper bound on ||s0||^2 + ||s1||^2
// - sigbytelen is the bytelength of signatures
type PublicParameters struct {
	n          uint16
	sigma      float64
	sigmin     float64
	sigbound   uint32
	sigbytelen uint16
}

var ParamSets = map[uint16]PublicParameters{
	// FalconParam(2, 2)
	2: {
		n:          2,
		sigma:      144.81253976308423,
		sigmin:     1.1165085072329104,
		sigbound:   101498,
		sigbytelen: 44,
	},
	// FalconParam(4, 2)
	4: {
		n:          4,
		sigma:      146.83798833523608,
		sigmin:     1.1321247692325274,
		sigbound:   208714,
		sigbytelen: 47,
	},
	// FalconParam(8, 2)
	8: {
		n:          8,
		sigma:      148.83587593064718,
		sigmin:     1.147528535373367,
		sigbound:   428865,
		sigbytelen: 52,
	},
	// FalconParam(16, 4)
	16: {
		n:          16,
		sigma:      151.78340713845503,
		sigmin:     1.170254078853483,
		sigbound:   892039,
		sigbytelen: 63,
	},
	// FalconParam(32, 8)
	32: {
		n:          32,
		sigma:      154.6747794602761,
		sigmin:     1.1925466358390344,
		sigbound:   1852696,
		sigbytelen: 82,
	},
	// FalconParam(64, 16)
	64: {
		n:          64,
		sigma:      157.51308555044122,
		sigmin:     1.2144300507766141,
		sigbound:   3842630,
		sigbytelen: 122,
	},
	// FalconParam(128, 32)
	128: {
		n:          128,
		sigma:      160.30114421975344,
		sigmin:     1.235926056771981,
		sigbound:   7959734,
		sigbytelen: 200,
	},
	// FalconParam(256, 64)
	256: {
		n:          256,
		sigma:      163.04153322607107,
		sigmin:     1.2570545284063217,
		sigbound:   16468416,
		sigbytelen: 356,
	},
	// FalconParam(512, 128)
	512: {
		n:          512,
		sigma:      165.7366171829776,
		sigmin:     1.2778336969128337,
		sigbound:   34034726,
		sigbytelen: 666,
	},
	// FalconParam(1024, 256)
	1024: {
		n:          1024,
		sigma:      168.38857144654395,
		sigmin:     1.298280334344292,
		sigbound:   70265242,
		sigbytelen: 1280,
	},
}
