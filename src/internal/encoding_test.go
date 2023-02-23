package internal

import (
	"bytes"
	"reflect"
	"testing"
)

var (
// n int = 64
// iterations int = 1
)

func TestCompress(t *testing.T) {
	testCases := []struct {
		v        []int16
		slen     int
		expected []byte
		err      error
	}{
		{
			// Test case 1
			v:        []int16{176, -210, 53, 15, -91, -305, 324, 252, -30, 5, -83, 272, 0, 93, -117, 196, 22, 229, -217, -204, 5, -232, 61, -203, -27, -129, 28, -42, 81, 20, -23, -88, 255, -75, 10, 233, 54, 1, 32, 48, 157, -124, -231, -159, -123, 94, -112, -246, 146, 46, -179, 282, -67, 114, -139, -122, -51, 443, 171, 23, 397, 180, -15, 67},
			slen:     81,
			expected: []byte{48, 116, 147, 88, 127, 111, 98, 81, 11, 227, 61, 5, 233, 196, 8, 5, 119, 235, 68, 69, 172, 174, 203, 152, 130, 250, 19, 222, 91, 55, 129, 71, 53, 85, 24, 166, 95, 177, 127, 114, 225, 86, 148, 218, 3, 32, 152, 71, 95, 207, 59, 62, 253, 215, 190, 31, 100, 73, 46, 217, 163, 71, 14, 229, 139, 126, 182, 115, 177, 43, 69, 225, 162, 104, 199, 208, 224, 0, 0, 0, 0},
			err:      nil,
		},
		{
			// Test case 2
			v:        []int16{128, 256, 512, 1024},
			slen:     2,
			expected: nil,
			err:      ErrEncodingTooLong,
		},
	}
	for _, tc := range testCases {
		result, err := Compress(tc.v, tc.slen)

		if err != tc.err {
			t.Errorf("Expected error value %v, got %v", tc.err, err)
		}
		if !bytes.Equal(result, tc.expected) {
			t.Errorf("Expected %v, got %v", tc.expected, result)
		}
	}
}

func TestDecompress(t *testing.T) {
	testCases := []struct {
		x        []byte
		slen     int
		n        int
		expected []int
		err      error
	}{
		{
			// Test case 1
			x:        []byte{85, 198, 106, 215, 19, 11, 127, 229, 79, 178, 214, 39, 138, 192, 231, 81, 170, 61, 121, 143, 220, 161, 182, 200, 11, 137, 218, 228, 105, 90, 136, 246, 119, 125, 14, 67, 93, 170, 47, 204, 180, 202, 202, 135, 115, 65, 237, 179, 226, 160, 48, 130, 206, 158, 255, 162, 2, 104, 178, 235, 203, 11, 237, 169, 164, 165, 145, 239, 44, 43, 240, 147, 37, 235, 115, 159, 0, 0, 0, 0, 0},
			slen:     81,
			n:        64,
			expected: []int{85, -12, -171, 369, -5, 127, -74, 62, -22, 226, -98, 224, -78, 70, 81, -87, 49, -375, 195, -182, 129, -68, -90, -72, -165, -40, 30, -29, -62, 142, 141, -90, 69, -371, 105, 299, 80, -92, -32, -109, 103, -10, 1, 264, 231, 61, -126, 400, 180, 101, -303, 225, -118, -41, 201, 44, 30, -101, 10, -248, 166, 175, 238, -79},
			err:      nil,
		},
		//{
		//	// Test case 2
		//	v:        []int{128, 256, 512, 1024},
		//	slen:     2,
		//	expected: nil,
		//	err:      ErrEncodingTooLong,
		//},
	}
	for _, tc := range testCases {
		result, err := Decompress(tc.x, tc.slen, tc.n)
		if err != tc.err {
			t.Errorf("Expected error value %v, got %v", tc.err, err)
		}
		if !reflect.DeepEqual(result, tc.expected) {
			t.Errorf("Expected %v, got %v", tc.expected, result)
		}
	}
}
