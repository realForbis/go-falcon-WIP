package internal

import (
	"log"
	"math/big"
	"reflect"
	"testing"

	"github.com/realForbis/go-falcon/src/types"
	"github.com/realForbis/go-falcon/src/util"
)

func TestKaratsuba(t *testing.T) {
	tests := []struct {
		a, b []*big.Int // input numbers
		n    int        // length of input numbers
		want []*big.Int // expected output
	}{
		{ // test case 1
			[]*big.Int{big.NewInt(-1722293), big.NewInt(4178192), big.NewInt(-9649111), big.NewInt(23373769), big.NewInt(-3043485), big.NewInt(-7818004), big.NewInt(9749573), big.NewInt(-11142221)},
			[]*big.Int{big.NewInt(-1722293), big.NewInt(4178192), big.NewInt(-9649111), big.NewInt(23373769), big.NewInt(-3043485), big.NewInt(-7818004), big.NewInt(9749573), big.NewInt(-11142221)},
			8,
			[]*big.Int{big.NewInt(2966293177849), big.NewInt(-14392141668512), big.NewInt(50694481051910), big.NewInt(-161144634239258), big.NewInt(298909078203827), big.NewInt(-449574925370614), big.NewInt(506153440249717), big.NewInt(128449660388496), big.NewInt(-637467739576997), big.NewInt(718381544540216), big.NewInt(-519095571421692), big.NewInt(-84622036464214), big.NewInt(269274030376097), big.NewInt(-217263794043266), big.NewInt(124149088812841), big.NewInt(0)},
		},
		{ // test case 2
			[]*big.Int{types.NewBigIntFromString("52338756788524724890787105069"), types.NewBigIntFromString("648491287334163971732428693477")},
			[]*big.Int{types.NewBigIntFromString("52338756788524724890787105069"), types.NewBigIntFromString("648491287334163971732428693477")},
			2,
			[]*big.Int{types.NewBigIntFromString("2739345462168342973823307644396997456086118469209645494761"), types.NewBigIntFromString("67882455534520225039477001526435245573042659757693587869826"), types.NewBigIntFromString("420540949748321217307254166141247872707684025362425222349529"), types.NewBigIntFromString("0")},
		},
		{ // test case 3
			[]*big.Int{types.NewBigIntFromString("19478150517288854163173047302489688112904458986479828421220")},
			[]*big.Int{types.NewBigIntFromString("19478150517288854163173047302489688112904458986479828421220")},
			1,
			[]*big.Int{types.NewBigIntFromString("379398347574160057024576824078492349243547563079081823562489162322150136820909608566446443524131479479650477746288400"), big.NewInt(0)},
		},
	}

	for _, test := range tests {
		got := Karatsuba(test.a, test.b, test.n)
		if !reflect.DeepEqual(got, test.want) {
			t.Errorf("Karatsuba(%v, %v, %v) = %v; want %v", test.a, test.b, test.n, got, test.want)
		}
	}
}

func TestKaramul(t *testing.T) {
	tests := []struct {
		a, b []*big.Int // input numbers
		want []*big.Int // expected output
	}{
		{ // test case 1
			[]*big.Int{big.NewInt(-17219037), big.NewInt(10276473), big.NewInt(-445972), big.NewInt(-26217107), big.NewInt(23002005), big.NewInt(11044591), big.NewInt(-26663538), big.NewInt(-5297245)},
			[]*big.Int{big.NewInt(-17219037), big.NewInt(10276473), big.NewInt(-445972), big.NewInt(-26217107), big.NewInt(23002005), big.NewInt(11044591), big.NewInt(-26663538), big.NewInt(-5297245)},
			[]*big.Int{big.NewInt(431609056919716), big.NewInt(-2264803915826324), big.NewInt(947854114547326), big.NewInt(1726370888096772), big.NewInt(-1924717093534662), big.NewInt(-166697870920616), big.NewInt(1783999171672602), big.NewInt(-1581530550650792)},
		},
		{ // test case 2
			[]*big.Int{types.NewBigIntFromString("53349370353379628213864895893969560559002040512179219164408")},
			[]*big.Int{types.NewBigIntFromString("53349370353379628213864895893969560559002040512179219164408")},
			[]*big.Int{types.NewBigIntFromString("2846155317102061196964996558687104462276788583144141797371630925119066320037553006198831820309887328502683101733990464")},
		},
	}

	for _, test := range tests {
		got := karamul(test.a, test.b)
		if !reflect.DeepEqual(got, test.want) {
			t.Errorf("karamul(%v, %v) = %v; want %v", test.a, test.b, got, test.want)
		}
	}
}

func TestGaloisConjugate(t *testing.T) {
	tests := []struct {
		a    []*big.Int // input numbers
		want []*big.Int // expected output
	}{
		{ // test case 1
			[]*big.Int{big.NewInt(-1732), big.NewInt(-181), big.NewInt(292), big.NewInt(-130), big.NewInt(-1647), big.NewInt(199), big.NewInt(-1385), big.NewInt(-558), big.NewInt(-309), big.NewInt(1833), big.NewInt(-401), big.NewInt(850), big.NewInt(253), big.NewInt(-36), big.NewInt(-2597), big.NewInt(2510), big.NewInt(-719), big.NewInt(925), big.NewInt(20), big.NewInt(1790), big.NewInt(-1794), big.NewInt(494), big.NewInt(130), big.NewInt(1425), big.NewInt(-1482), big.NewInt(83), big.NewInt(795), big.NewInt(-887), big.NewInt(-1940), big.NewInt(744), big.NewInt(185), big.NewInt(-1032)},
			[]*big.Int{big.NewInt(-1732), big.NewInt(181), big.NewInt(292), big.NewInt(130), big.NewInt(-1647), big.NewInt(-199), big.NewInt(-1385), big.NewInt(558), big.NewInt(-309), big.NewInt(-1833), big.NewInt(-401), big.NewInt(-850), big.NewInt(253), big.NewInt(36), big.NewInt(-2597), big.NewInt(-2510), big.NewInt(-719), big.NewInt(-925), big.NewInt(20), big.NewInt(-1790), big.NewInt(-1794), big.NewInt(-494), big.NewInt(130), big.NewInt(-1425), big.NewInt(-1482), big.NewInt(-83), big.NewInt(795), big.NewInt(887), big.NewInt(-1940), big.NewInt(-744), big.NewInt(185), big.NewInt(1032)},
		},
		{ // test case 2
			[]*big.Int{types.NewBigIntFromString("39812503573841235691159909287661889976438046641922619875"), types.NewBigIntFromString("-805322007111735017663100393021532665363771297089472824597")},
			[]*big.Int{types.NewBigIntFromString("39812503573841235691159909287661889976438046641922619875"), types.NewBigIntFromString("805322007111735017663100393021532665363771297089472824597")},
		},
	}

	for _, test := range tests {
		got := galoisConjugate(test.a)
		if !reflect.DeepEqual(got, test.want) {
			t.Errorf("galoisConjugate(%v) = %v; want %v", test.a, got, test.want)
		}
	}
}

func TestFieldNorm(t *testing.T) {
	tests := []struct {
		a    []*big.Int // input numbers
		want []*big.Int // expected output
	}{
		{ // test case 1
			[]*big.Int{types.NewBigIntFromString("-1503750261189601"), types.NewBigIntFromString("2942249559750856"), types.NewBigIntFromString("-950969046985171"), types.NewBigIntFromString("-1929426619933851"), types.NewBigIntFromString("3254733311432332"), types.NewBigIntFromString("191308165933376"), types.NewBigIntFromString("-3089736379163105"), types.NewBigIntFromString("1961215717985205")},
			[]*big.Int{types.NewBigIntFromString("-3405969370664081230755793101925"), types.NewBigIntFromString("6784298454259322286184414510992"), types.NewBigIntFromString("-6326638488578950583559477843776"), types.NewBigIntFromString("2100009780394092918217943106778")},
		},
		{ // test case 2
			[]*big.Int{types.NewBigIntFromString("68459002847536195322714061137808019102920809174255398175001"), types.NewBigIntFromString("1480009384014221455342939305426559802814151730433175410454820")},
			[]*big.Int{types.NewBigIntFromString("2195114411841034199623234217635396841835966368689602380272638184433024161638837944381599118511403912684647922000682582401")},
		},
	}

	for _, test := range tests {
		got := fieldNorm(test.a)
		if !reflect.DeepEqual(got, test.want) {
			t.Errorf("fieldNorm(%v) = %v; want %v", test.a, got, test.want)
		}
	}
}

func TestLift(t *testing.T) {
	tests := []struct {
		a    []*big.Int // input numbers
		want []*big.Int // expected output
	}{
		{ // test case
			[]*big.Int{types.NewBigIntFromString("345590124733150545911158363977044097771109871084959531865242595729340005426946478559560831106294452323269899619034499140898601775794825066303869969198270680289236364386484845900207307716606874087547419357167"), types.NewBigIntFromString("1033648657894789404191452263509929711039858189541568403141974126456830643840975351226212290227307745853095084260452281271782700817696987902783645025760477983026816589331175097644724128962727724031534527634758"), types.NewBigIntFromString("-1807417330293339276542215798179684549240468291140110196763657482033347752036646302644199087727484036304843989833052201921469241935817128975491982042823835081938866741142643008130286405653099556962648230082473"), types.NewBigIntFromString("1522398829474937174752514074295914146087528416212951175173865544993916019515290243418081266674667157560501814098669779056559570267920398103828947498572114350277892823021301990644421491458360014947916271367035")},
			[]*big.Int{types.NewBigIntFromString("345590124733150545911158363977044097771109871084959531865242595729340005426946478559560831106294452323269899619034499140898601775794825066303869969198270680289236364386484845900207307716606874087547419357167"), types.NewBigIntFromString("0"), types.NewBigIntFromString("1033648657894789404191452263509929711039858189541568403141974126456830643840975351226212290227307745853095084260452281271782700817696987902783645025760477983026816589331175097644724128962727724031534527634758"), types.NewBigIntFromString("0"), types.NewBigIntFromString("-1807417330293339276542215798179684549240468291140110196763657482033347752036646302644199087727484036304843989833052201921469241935817128975491982042823835081938866741142643008130286405653099556962648230082473"), types.NewBigIntFromString("0"), types.NewBigIntFromString("1522398829474937174752514074295914146087528416212951175173865544993916019515290243418081266674667157560501814098669779056559570267920398103828947498572114350277892823021301990644421491458360014947916271367035"), types.NewBigIntFromString("0")},
		},
	}

	for _, test := range tests {
		got := lift(test.a)
		if !reflect.DeepEqual(got, test.want) {
			t.Errorf("lift(%v) = %v; want %v", test.a, got, test.want)
		}
	}
}

func TestBitsize(t *testing.T) {
	have := types.NewBigIntFromString("-11614318471081991024454905323819239514787274382547283788218123246560041300410847942656630218976410208078498063447686772197316541292721999312280856585757208838431316674765572320819680") // input number
	want := 608                                                                                                                                                                                                                  // expected output

	got := bitsize(have)
	if got != want {
		t.Errorf("bitsize(%v) = %v; want %v", have, got, want)
	}

}

func TestReduce(t *testing.T) {
	// input
	f := []*big.Int{types.NewBigIntFromString("8167204273898636560048286674269879285798731281831022589531"), types.NewBigIntFromString("52903525881878968008001655281131121416363796413648844592755")}
	g := []*big.Int{types.NewBigIntFromString("-15211881899369536835222895078659151459977910821792656733976"), types.NewBigIntFromString("16512908104586851150635870399127032751015060178024970692641")}
	F := []*big.Int{types.NewBigIntFromString("114549301782718162157739728510405813434881080370559319264348726366089823543495220224907785396155768870510647987961585949473882201375067896621756004760119769984634076033322739716312"), types.NewBigIntFromString("124346356768718246110966670766627670999060289441799591331743609448136101220205615472988642993396249749645908819562250458410893976458061021208238144015011987017985987603348560417417")}
	G := []*big.Int{types.NewBigIntFromString("-10818869602057653521486941953540019149979400701959749432093452450347691544182359110955340866158625618311406577024288592025912566838894732431696555018517172306324993185587602239420"), types.NewBigIntFromString("70079837458493598783606884232162264919646203879371898565925122531963372012913596746248357800194045115601498274913447956020501265195675764301097512991134332460290158276349010579100")}
	// expected output
	wantF := []*big.Int{types.NewBigIntFromString("-43150583716717049260335321370041691775103134611163843489542832812263987393799277652707113291477553271044685637565580570170955107367574023479478106597173121432886999914787829821224"), types.NewBigIntFromString("8825995750454300785746328558410336566777310493701231945740604949272507265560282484297211648083385493239558454950729915089921947533585075068171392481871192905106788379463569773193")}
	wantG := []*big.Int{types.NewBigIntFromString("-14178444361867936728550580251237620567331442683458875845939207937460339263013047585117726029755058259483722632571148676914260422880308655696063769811141966742476906724222027542460"), types.NewBigIntFromString("-11841497661555560366571630736833760042655682201071469846579326213080050165167425996148072149310564764072517047467329654067354516002015316022779409127208776253287576611807123009892")}

	gotF, gotG := reduce(f, g, F, G)
	if !util.BigIntSliceEqual(gotF, wantF) || !util.BigIntSliceEqual(gotG, wantG) {
		t.Errorf("reduce(%v, %v, %v, %v) = %v, %v; want %v, %v", f, g, F, G, gotF, gotG, wantF, wantG)
	}
}

func TestXgcd(t *testing.T) {
	// input
	b := types.NewBigIntFromString("1145340830882995436378811904538856938868078888206737517383606322715260379248994177843057545761073726624250782868170753")
	n := types.NewBigIntFromString("9486361600165354555722060686294546917519437196222743348218185598186294869424452895957595047627164285123501655417062657")
	// expected output
	wantD := types.NewBigIntFromString("257")
	wantU := types.NewBigIntFromString("1887568559923859650483546522790283789280349088471127254174909938921149613092025877546030982861814662354609056756622")
	wantV := types.NewBigIntFromString("-227896577622987598934643379431709599769219034688896412024872634276960649796595978245643891138947363474318309335437")

	gotD, gotU, gotV := xgcd(b, n)
	if !util.CmpBigInt(gotD, wantD) || !util.CmpBigInt(gotU, wantU) || !util.CmpBigInt(gotV, wantV) {
		t.Errorf("Got: %v, %v, %v; want %v, %v, %v", gotD, gotU, gotV, wantD, wantU, wantV)
	}
}

func TestNtruSolve(t *testing.T) {
	testCases := []struct {
		f     []*big.Int
		g     []*big.Int
		wantF []*big.Int
		wantG []*big.Int
		err   error
	}{
		{
			// Test case 1
			f:     []*big.Int{big.NewInt(16), big.NewInt(-3), big.NewInt(-19), big.NewInt(11), big.NewInt(2), big.NewInt(8), big.NewInt(9), big.NewInt(-14), big.NewInt(-12), big.NewInt(1), big.NewInt(-3), big.NewInt(2), big.NewInt(4), big.NewInt(-13), big.NewInt(-1), big.NewInt(-5), big.NewInt(-3), big.NewInt(-10), big.NewInt(18), big.NewInt(2), big.NewInt(-17), big.NewInt(6), big.NewInt(1), big.NewInt(1), big.NewInt(-9), big.NewInt(10), big.NewInt(6), big.NewInt(13), big.NewInt(22), big.NewInt(13), big.NewInt(1), big.NewInt(-12), big.NewInt(10), big.NewInt(-6), big.NewInt(-27), big.NewInt(11), big.NewInt(18), big.NewInt(0), big.NewInt(-14), big.NewInt(3), big.NewInt(-3), big.NewInt(12), big.NewInt(-15), big.NewInt(-9), big.NewInt(19), big.NewInt(6), big.NewInt(28), big.NewInt(6), big.NewInt(-13), big.NewInt(19), big.NewInt(2), big.NewInt(3), big.NewInt(-1), big.NewInt(6), big.NewInt(-2), big.NewInt(-20), big.NewInt(-5), big.NewInt(26), big.NewInt(5), big.NewInt(-2), big.NewInt(13), big.NewInt(-10), big.NewInt(0), big.NewInt(1)},
			g:     []*big.Int{big.NewInt(5), big.NewInt(-3), big.NewInt(2), big.NewInt(4), big.NewInt(12), big.NewInt(17), big.NewInt(-3), big.NewInt(-16), big.NewInt(6), big.NewInt(-18), big.NewInt(2), big.NewInt(-12), big.NewInt(29), big.NewInt(-4), big.NewInt(9), big.NewInt(-8), big.NewInt(0), big.NewInt(0), big.NewInt(5), big.NewInt(-4), big.NewInt(-5), big.NewInt(5), big.NewInt(5), big.NewInt(-2), big.NewInt(21), big.NewInt(5), big.NewInt(8), big.NewInt(-7), big.NewInt(-6), big.NewInt(-17), big.NewInt(4), big.NewInt(2), big.NewInt(-5), big.NewInt(15), big.NewInt(-6), big.NewInt(-14), big.NewInt(-2), big.NewInt(10), big.NewInt(8), big.NewInt(-8), big.NewInt(-18), big.NewInt(24), big.NewInt(-4), big.NewInt(-7), big.NewInt(-10), big.NewInt(15), big.NewInt(0), big.NewInt(23), big.NewInt(10), big.NewInt(2), big.NewInt(17), big.NewInt(-2), big.NewInt(-21), big.NewInt(-7), big.NewInt(-12), big.NewInt(-5), big.NewInt(3), big.NewInt(1), big.NewInt(14), big.NewInt(3), big.NewInt(-1), big.NewInt(-3), big.NewInt(-13), big.NewInt(6)},
			wantF: []*big.Int{big.NewInt(8), big.NewInt(31), big.NewInt(11), big.NewInt(-16), big.NewInt(11), big.NewInt(11), big.NewInt(6), big.NewInt(-5), big.NewInt(30), big.NewInt(-8), big.NewInt(15), big.NewInt(8), big.NewInt(16), big.NewInt(64), big.NewInt(45), big.NewInt(14), big.NewInt(46), big.NewInt(20), big.NewInt(-17), big.NewInt(43), big.NewInt(8), big.NewInt(-29), big.NewInt(40), big.NewInt(45), big.NewInt(-7), big.NewInt(-6), big.NewInt(5), big.NewInt(-4), big.NewInt(-20), big.NewInt(-16), big.NewInt(6), big.NewInt(-14), big.NewInt(-22), big.NewInt(24), big.NewInt(13), big.NewInt(-25), big.NewInt(54), big.NewInt(8), big.NewInt(18), big.NewInt(20), big.NewInt(17), big.NewInt(31), big.NewInt(-8), big.NewInt(-45), big.NewInt(-19), big.NewInt(-12), big.NewInt(-28), big.NewInt(4), big.NewInt(-24), big.NewInt(-2), big.NewInt(52), big.NewInt(-18), big.NewInt(-18), big.NewInt(-11), big.NewInt(22), big.NewInt(1), big.NewInt(-5), big.NewInt(-20), big.NewInt(-6), big.NewInt(1), big.NewInt(24), big.NewInt(75), big.NewInt(11), big.NewInt(-10)},
			wantG: []*big.Int{big.NewInt(37), big.NewInt(49), big.NewInt(31), big.NewInt(17), big.NewInt(-31), big.NewInt(-22), big.NewInt(-7), big.NewInt(-35), big.NewInt(-9), big.NewInt(47), big.NewInt(-3), big.NewInt(26), big.NewInt(19), big.NewInt(34), big.NewInt(64), big.NewInt(-7), big.NewInt(3), big.NewInt(-36), big.NewInt(-68), big.NewInt(-66), big.NewInt(-34), big.NewInt(2), big.NewInt(25), big.NewInt(-28), big.NewInt(-7), big.NewInt(12), big.NewInt(57), big.NewInt(-23), big.NewInt(2), big.NewInt(-44), big.NewInt(-30), big.NewInt(-23), big.NewInt(-11), big.NewInt(-34), big.NewInt(49), big.NewInt(-8), big.NewInt(14), big.NewInt(12), big.NewInt(15), big.NewInt(-50), big.NewInt(22), big.NewInt(-46), big.NewInt(3), big.NewInt(-51), big.NewInt(-14), big.NewInt(-8), big.NewInt(13), big.NewInt(-12), big.NewInt(34), big.NewInt(-14), big.NewInt(32), big.NewInt(14), big.NewInt(-14), big.NewInt(-40), big.NewInt(-13), big.NewInt(7), big.NewInt(16), big.NewInt(9), big.NewInt(15), big.NewInt(8), big.NewInt(60), big.NewInt(-18), big.NewInt(24), big.NewInt(-27)},
			err:   nil,
		},
		{
			// Test case 2
			f:     []*big.Int{big.NewInt(8), big.NewInt(6), big.NewInt(2), big.NewInt(10), big.NewInt(6), big.NewInt(19), big.NewInt(-3), big.NewInt(8), big.NewInt(7), big.NewInt(-1), big.NewInt(-2), big.NewInt(-1), big.NewInt(13), big.NewInt(15), big.NewInt(-7), big.NewInt(8), big.NewInt(-1), big.NewInt(-5), big.NewInt(-17), big.NewInt(15), big.NewInt(20), big.NewInt(3), big.NewInt(12), big.NewInt(7), big.NewInt(15), big.NewInt(26), big.NewInt(7), big.NewInt(-6), big.NewInt(-1), big.NewInt(2), big.NewInt(-10), big.NewInt(1), big.NewInt(4), big.NewInt(6), big.NewInt(16), big.NewInt(-3), big.NewInt(7), big.NewInt(13), big.NewInt(5), big.NewInt(-4), big.NewInt(-18), big.NewInt(-10), big.NewInt(9), big.NewInt(11), big.NewInt(-16), big.NewInt(2), big.NewInt(-11), big.NewInt(9), big.NewInt(3), big.NewInt(10), big.NewInt(-3), big.NewInt(-6), big.NewInt(3), big.NewInt(11), big.NewInt(-4), big.NewInt(-3), big.NewInt(-4), big.NewInt(4), big.NewInt(-3), big.NewInt(19), big.NewInt(1), big.NewInt(19), big.NewInt(8), big.NewInt(7)},
			g:     []*big.Int{big.NewInt(3), big.NewInt(5), big.NewInt(7), big.NewInt(11), big.NewInt(13), big.NewInt(3), big.NewInt(-7), big.NewInt(9), big.NewInt(-22), big.NewInt(13), big.NewInt(22), big.NewInt(-17), big.NewInt(19), big.NewInt(-4), big.NewInt(0), big.NewInt(21), big.NewInt(-10), big.NewInt(15), big.NewInt(8), big.NewInt(-2), big.NewInt(28), big.NewInt(9), big.NewInt(-4), big.NewInt(-9), big.NewInt(-13), big.NewInt(-3), big.NewInt(-18), big.NewInt(1), big.NewInt(1), big.NewInt(9), big.NewInt(-1), big.NewInt(9), big.NewInt(10), big.NewInt(9), big.NewInt(-17), big.NewInt(-2), big.NewInt(-2), big.NewInt(14), big.NewInt(14), big.NewInt(1), big.NewInt(0), big.NewInt(-2), big.NewInt(-4), big.NewInt(12), big.NewInt(22), big.NewInt(3), big.NewInt(-13), big.NewInt(29), big.NewInt(1), big.NewInt(-16), big.NewInt(-13), big.NewInt(-6), big.NewInt(-4), big.NewInt(6), big.NewInt(0), big.NewInt(6), big.NewInt(1), big.NewInt(11), big.NewInt(-18), big.NewInt(30), big.NewInt(-4), big.NewInt(0), big.NewInt(23), big.NewInt(-11)},
			wantF: nil,
			wantG: nil,
			err:   ErrEquation,
		},
	}

	// Iterate through test cases
	n := 0
	for _, tc := range testCases {
		// Call NtruSolve with test case inputs
		gotX, gotY, err := NtruSolve(tc.f, tc.g)

		// Check that the returned error value is as expected
		if err != tc.err {
			t.Errorf("Expected error value %v, got %v", tc.err, err)
		}

		// Check that the returned output is as expected
		if !reflect.DeepEqual(gotX, tc.wantF) || !reflect.DeepEqual(gotY, tc.wantG) {
			t.Errorf("Expected output %v, %v, got %v, %v", tc.wantF, tc.wantG, gotX, gotY)
		}
		t.Logf("Test case %v passed", n)
		n++
	}
}

func TestGsNorm(t *testing.T) {
	f := []float64{-8, -1, -1, 5, 25, 11, -5, -28, 0, 10, 12, 6, 23, -1, -1, -7, -25, -6, 24, 6, -18, 9, -1, 0, -2, -7, 3, -4, -9, 4, 7, -3, 13, -4, 0, 1, 20, -10, -3, 22, 22, -11, -27, -4, -5, -5, -19, 19, -6, 18, -3, -9, 9, 8, 13, 9, -15, 1, -5, -13, 8, -1, -6, 5}
	g := []float64{-1, -9, -17, -1, 12, 3, 1, -3, 13, -13, -25, 5, -14, 0, 22, -4, -4, 16, 1, 15, 9, 8, 13, 6, -3, -3, 10, -1, 3, 7, 0, -10, 12, 3, 7, -6, 1, -6, -2, 1, 17, 10, 4, -7, 6, 5, 8, -10, 11, -14, 5, 5, -5, 8, 4, 3, 1, 7, -6, 9, -10, -12, -1, -4}
	var q float64 = 12289
	want := 20662.220733723763

	got := GsNorm(f, g, q)
	if got != want {
		t.Errorf("GsNorm(%v, %v, %v) = %v; want %v", f, g, q, got, want)
	}
}

func TestGenPoly(t *testing.T) {
	var n uint16 = 64
	polys := GenPoly(n)
	log.Println(polys)
}

func TestNtruGen(t *testing.T) {
	t.Skip()
}
