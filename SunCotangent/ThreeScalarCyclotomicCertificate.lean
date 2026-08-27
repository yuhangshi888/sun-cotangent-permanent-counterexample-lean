import Mathlib.NumberTheory.LegendreSymbol.Basic
import SunCotangent.CertificateComplexBridge
import SunCotangent.CyclotomicLifting
import SunCotangent.GrayCheckpointFramework
import SunCotangent.ScalarSpecialization
import SunCotangent.PolynomialQuotientCertificate

/-!
# A second, independent three-scalar cyclotomic certificate

This module gives an independent kernel-checked route through Section 4.
It uses three pairwise-coprime 61-bit moduli which are all congruent to one
modulo 29.  Consequently each cyclotomic specialization is an ordinary
scalar permanent in the base residue ring.  The three permanents are packed
and evaluated by one Gray scan with 128 local checkpoints.

The middle-sized moduli `largeModulusA` and `largeModulusB` are deliberately
chosen for this formal verification.  The third is the second modulus used
by the paper's original C++ coefficient computation.  The paper's other two
original moduli and their printed residues remain formalized in
`OriginalCyclotomicModuli`; this module does not claim to replay those two
extension-valued C++ computations instruction by instruction.

No theorem here depends on the six-small-modulus permanent certificate,
`CertificateCRT.canonicalConstant_eq_claimed`, or the existing final theorem.
-/

open scoped BigOperators

namespace SunCotangent
namespace ThreeScalarCyclotomicCertificate

open CyclotomicCertificate
open LiteralSectionFourBounds
open OriginalCyclotomicModuli
open GrayCheckpointFramework

local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

/-! ## Moduli and scalar roots -/

def largeModulusA : ℕ := 1_154_171_649_327_628_289
def largeModulusB : ℕ := 1_155_638_397_839_081_473
abbrev largeModulusC : ℕ := paperModulus2

abbrev LargeResidueA := ZMod largeModulusA
abbrev LargeResidueB := ZMod largeModulusB
abbrev LargeResidueC := ZMod largeModulusC

def largeRootA : LargeResidueA := 379_504_592_072_158_685
def largeRootB : LargeResidueB := 179_111_278_102_344_668
def largeRootC : LargeResidueC := 941_577_490_928_837_153

theorem largeRootA_pow_twentyNine : largeRootA ^ 29 = 1 := by
  decide +kernel

theorem largeRootB_pow_twentyNine : largeRootB ^ 29 = 1 := by
  decide +kernel

theorem largeRootC_pow_twentyNine : largeRootC ^ 29 = 1 := by
  decide +kernel

theorem largeRootA_cyclotomic_sum :
    ∑ e : Z29, largeRootA ^ e.val = 0 := by
  decide +kernel

theorem largeRootB_cyclotomic_sum :
    ∑ e : Z29, largeRootB ^ e.val = 0 := by
  decide +kernel

theorem largeRootC_cyclotomic_sum :
    ∑ e : Z29, largeRootC ^ e.val = 0 := by
  decide +kernel

theorem evalRoot_cyclotomicSum_largeA :
    evalRoot largeModulusA largeRootA largeRootA_pow_twentyNine
      cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero largeModulusA largeRootA
    largeRootA_pow_twentyNine largeRootA_cyclotomic_sum

theorem evalRoot_cyclotomicSum_largeB :
    evalRoot largeModulusB largeRootB largeRootB_pow_twentyNine
      cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero largeModulusB largeRootB
    largeRootB_pow_twentyNine largeRootB_cyclotomic_sum

theorem evalRoot_cyclotomicSum_largeC :
    evalRoot largeModulusC largeRootC largeRootC_pow_twentyNine
      cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero largeModulusC largeRootC
    largeRootC_pow_twentyNine largeRootC_cyclotomic_sum

/-! ## Literal scalar entry tables -/

def largeEntryTableA : Z29 → LargeResidueA :=
  ![0, 409_802_875_405_201_973, 1_121_790_891_552_029_346,
    623_266_676_279_366_734, 861_411_356_337_463_409,
    569_264_358_514_749_609, 896_266_921_024_193_336,
    144_883_348_333_835_238, 916_254_614_218_058_072,
    324_601_911_949_830_893, 805_137_425_542_105_076,
    871_522_283_382_473_446, 232_673_047_143_218_516,
    611_871_165_341_293_850, 1_089_394_097_486_963_552,
    64_777_551_840_664_737, 542_300_483_986_334_439,
    921_498_602_184_409_773, 282_649_365_945_154_843,
    349_034_223_785_523_213, 829_569_737_377_797_396,
    237_917_035_109_570_217, 1_009_288_300_993_793_051,
    257_904_728_303_434_953, 584_907_290_812_878_680,
    292_760_292_990_164_880, 530_904_973_048_261_555,
    32_380_757_775_598_943, 744_368_773_922_426_316]

def largeEntryTableB : Z29 → LargeResidueB :=
  ![0, 292_438_789_126_012_789, 1_048_093_377_656_148_283,
    1_039_119_890_180_255_373, 909_240_733_666_017_870,
    226_754_566_256_919_644, 140_212_957_147_149_169,
    347_658_049_363_455_942, 924_373_132_370_049_230,
    786_539_209_636_379_373, 298_506_262_199_828_652,
    93_416_838_770_354_092, 234_313_180_395_857_883,
    97_937_542_516_496_850, 901_184_806_871_490_901,
    254_453_590_967_590_572, 1_057_700_855_322_584_623,
    921_325_217_443_223_590, 1_062_221_559_068_727_381,
    857_132_135_639_252_821, 369_099_188_202_702_100,
    231_265_265_469_032_243, 807_980_348_475_625_531,
    1_015_425_440_691_932_304, 928_883_831_582_161_829,
    246_397_664_173_063_603, 116_518_507_658_826_100,
    107_545_020_182_933_190, 863_199_608_713_068_684]

def largeEntryTableC : Z29 → LargeResidueC :=
  ![0, 590_988_667_145_463_331, 947_016_624_779_673_278,
    1_310_384_815_617_240_050, 1_664_147_581_120_267_545,
    2_251_442_466_759_795_978, 1_481_708_639_171_022_933,
    1_647_227_783_239_184_660, 2_242_510_008_139_456_788,
    686_577_513_437_683_685, 533_605_468_996_850_870,
    596_002_154_698_013_596, 581_158_101_867_999_104,
    1_269_343_050_471_388_013, 1_764_229_127_003_104_389,
    541_613_882_210_589_532, 1_036_499_958_742_305_908,
    1_724_684_907_345_694_817, 1_709_840_854_515_680_325,
    1_772_237_540_216_843_051, 1_619_265_495_776_010_236,
    63_333_001_074_237_133, 658_615_225_974_509_261,
    824_134_370_042_670_988, 54_400_542_453_897_943,
    641_695_428_093_426_376, 995_458_193_596_453_871,
    1_358_826_384_434_020_643, 1_714_854_342_068_230_590]

theorem largeEntryTableA_correct : ∀ e : Z29,
    largeEntryTableA e = scalarEntry largeModulusA largeRootA e := by
  decide +kernel

theorem largeEntryTableB_correct : ∀ e : Z29,
    largeEntryTableB e = scalarEntry largeModulusB largeRootB e := by
  decide +kernel

theorem largeEntryTableC_correct : ∀ e : Z29,
    largeEntryTableC e = scalarEntry largeModulusC largeRootC e := by
  decide +kernel

def largeResidueMatrixA : Matrix (Fin 14) (Fin 14) LargeResidueA :=
  fun i j ↦ largeEntryTableA
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

def largeResidueMatrixB : Matrix (Fin 14) (Fin 14) LargeResidueB :=
  fun i j ↦ largeEntryTableB
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

def largeResidueMatrixC : Matrix (Fin 14) (Fin 14) LargeResidueC :=
  fun i j ↦ largeEntryTableC
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem scalarMatrix_largeA :
    scalarMatrix largeModulusA largeRootA = largeResidueMatrixA := by
  ext i j
  simp only [scalarMatrix, largeResidueMatrixA]
  exact (largeEntryTableA_correct _).symm

theorem scalarMatrix_largeB :
    scalarMatrix largeModulusB largeRootB = largeResidueMatrixB := by
  ext i j
  simp only [scalarMatrix, largeResidueMatrixB]
  exact (largeEntryTableB_correct _).symm

theorem scalarMatrix_largeC :
    scalarMatrix largeModulusC largeRootC = largeResidueMatrixC := by
  ext i j
  simp only [scalarMatrix, largeResidueMatrixC]
  exact (largeEntryTableC_correct _).symm

def largeGaussValueA : LargeResidueA := 1_079_961_013_824_279_081
def largeGaussValueB : LargeResidueB := 324_694_811_615_532_670
def largeGaussValueC : LargeResidueC := 1_305_746_601_105_774_698

def largePermanentValueA : LargeResidueA := 534_563_429_140_343_107
def largePermanentValueB : LargeResidueB := 782_586_125_134_744_552
def largePermanentValueC : LargeResidueC := 894_844_875_296_022_347

def largeCertificateResidueA : LargeResidueA := 994_781_469_474_932_964
def largeCertificateResidueB : LargeResidueB := 89_419_196_786_011_049
def largeCertificateResidueC : LargeResidueC := 581_251_497_600_139_858

theorem scalarGauss_largeA :
    scalarGauss largeModulusA largeRootA = largeGaussValueA := by
  decide +kernel

theorem scalarGauss_largeB :
    scalarGauss largeModulusB largeRootB = largeGaussValueB := by
  decide +kernel

theorem scalarGauss_largeC :
    scalarGauss largeModulusC largeRootC = largeGaussValueC := by
  decide +kernel

/-! ## One packed Gray computation -/

abbrev LargePack :=
  LargeResidueA × (LargeResidueB × LargeResidueC)

def largePackMatrix : Matrix (Fin 14) (Fin 14) LargePack :=
  fun i j ↦
    (largeResidueMatrixA i j,
      (largeResidueMatrixB i j, largeResidueMatrixC i j))

def expectedLargePermanent : LargePack :=
  (largePermanentValueA,
    (largePermanentValueB, largePermanentValueC))

private def checkpointValue (a b c : ℕ) : LargePack :=
  (a, (b, c))

private def checkpointAccumulator : Fin 129 → LargePack :=
  ![checkpointValue 198_209_142_651_950_558 959_075_962_257_512_332 1_690_671_718_149_084_297,
    checkpointValue 1_071_972_982_319_863_290 446_421_324_328_473_185 1_519_074_902_739_598_432,
    checkpointValue 357_443_320_485_814_787 225_766_895_180_652_552 1_704_765_527_800_187_883,
    checkpointValue 35_448_483_319_910_014 9_059_751_516_251_754 1_979_940_267_746_230_545,
    checkpointValue 844_043_295_721_696_592 46_576_977_923_084_423 1_930_897_887_240_895_568,
    checkpointValue 19_883_603_701_783_093 1_142_697_011_996_014_178 155_578_154_671_628_305,
    checkpointValue 673_204_195_663_935_908 349_268_575_900_917_439 266_904_051_478_997_181,
    checkpointValue 1_037_381_936_100_196_632 695_087_723_157_497_647 35_112_830_369_745_085,
    checkpointValue 982_267_332_245_547_090 1_030_573_477_354_330_155 520_090_587_714_661_433,
    checkpointValue 473_616_088_916_806_848 892_779_998_960_439_033 597_699_728_837_160_506,
    checkpointValue 256_597_980_279_829_945 974_405_331_558_837_657 422_656_335_508_900_744,
    checkpointValue 784_323_815_597_881_979 123_571_760_885_861_510 1_679_908_251_181_396_091,
    checkpointValue 888_500_593_592_254_748 81_601_234_153_443_161 1_594_754_405_533_208_501,
    checkpointValue 658_941_784_343_942_801 863_695_037_906_496_188 238_562_669_451_372_387,
    checkpointValue 374_556_675_968_670_576 668_312_593_217_324_991 1_802_092_331_075_612_044,
    checkpointValue 1_037_580_273_756_212_730 450_870_965_009_380_345 2_053_314_291_387_398_457,
    checkpointValue 73_642_577_427_032_588 205_518_077_208_289_714 1_473_325_033_190_623_034,
    checkpointValue 350_008_612_988_213_054 225_334_894_635_089_164 1_817_981_385_011_158_218,
    checkpointValue 804_999_771_542_092_935 602_190_482_032_319_169 738_371_594_004_550_510,
    checkpointValue 965_801_116_894_341_685 19_445_739_149_063_385 1_901_765_268_804_469_999,
    checkpointValue 845_564_825_310_304_515 858_802_171_547_754_656 1_599_755_519_101_983_398,
    checkpointValue 143_870_376_196_810_936 571_131_437_473_903_381 2_056_616_213_724_131_293,
    checkpointValue 406_645_411_612_725_965 81_730_872_208_207_399 1_872_933_627_443_674_711,
    checkpointValue 737_602_925_945_057_545 1_083_502_056_468_328_435 1_504_963_864_824_486_010,
    checkpointValue 304_617_235_372_284_453 912_902_433_392_660_659 596_995_724_464_954_944,
    checkpointValue 1_028_823_853_002_574_654 100_157_446_130_715_837 249_675_549_026_821_434,
    checkpointValue 438_838_329_069_751_729 791_907_729_371_281_295 393_326_691_714_985_157,
    checkpointValue 311_896_221_143_539_165 220_243_795_779_862_896 1_703_931_508_953_796_193,
    checkpointValue 1_012_505_485_449_695_061 879_635_341_730_574_339 1_368_173_921_247_933_673,
    checkpointValue 51_348_654_492_889_983 266_827_808_129_133_365 1_375_513_225_385_967_307,
    checkpointValue 365_569_498_518_840_827 837_160_157_480_748_751 1_334_697_689_918_232_537,
    checkpointValue 546_420_832_060_993_461 873_880_844_184_446_468 691_966_074_356_318_280,
    checkpointValue 590_355_698_979_892_830 548_151_976_239_263_471 468_961_751_713_941_821,
    checkpointValue 89_770_447_974_556_285 485_365_810_456_470_613 503_784_015_645_157_061,
    checkpointValue 207_958_953_652_528_461 725_419_775_141_955_982 1_657_195_121_573_198_613,
    checkpointValue 846_148_356_961_194_206 391_382_857_607_813_013 690_067_679_252_467_733,
    checkpointValue 39_047_135_762_445_160 608_981_685_930_139_350 1_961_221_147_568_789_894,
    checkpointValue 136_124_310_533_915_046 163_478_691_052_047_285 1_096_788_058_229_861_544,
    checkpointValue 91_803_500_840_191_297 1_148_331_509_720_361_923 577_778_876_961_826_054,
    checkpointValue 51_046_181_579_550_138 114_689_646_404_638_285 2_286_827_287_577_268_074,
    checkpointValue 585_004_215_604_885_184 298_073_737_116_745_144 549_689_096_233_076_245,
    checkpointValue 797_098_768_673_287_731 784_411_227_612_935_163 544_831_120_813_858_838,
    checkpointValue 955_132_220_473_081_873 976_703_213_960_563_216 663_929_657_012_838_167,
    checkpointValue 218_643_659_772_470_310 14_861_335_159_857_145 758_360_765_527_337_432,
    checkpointValue 863_421_157_439_586_661 940_159_277_817_463_191 1_683_357_612_954_831_959,
    checkpointValue 1_143_076_354_092_310_877 546_533_569_130_623_369 1_980_318_803_090_005_791,
    checkpointValue 464_888_463_298_267_563 141_764_227_400_341_381 956_115_718_107_109_356,
    checkpointValue 468_406_102_140_661_225 845_604_252_887_619_185 816_416_217_749_794_411,
    checkpointValue 267_282_207_761_407_421 803_241_525_879_772_630 2_264_182_516_498_038_280,
    checkpointValue 545_617_363_537_065_671 152_704_260_550_053_354 1_080_304_108_359_661_959,
    checkpointValue 475_727_328_269_830_596 361_028_242_052_793_471 2_015_756_655_972_618_604,
    checkpointValue 934_889_399_771_869_147 780_980_091_290_770_921 974_400_763_966_024_004,
    checkpointValue 815_994_713_990_755_211 350_509_525_429_180_307 1_559_572_258_026_805_885,
    checkpointValue 857_895_921_070_928_017 656_686_728_051_144_992 1_458_446_013_408_913_214,
    checkpointValue 106_826_817_205_671_380 559_598_168_392_536_608 2_049_807_677_766_570_981,
    checkpointValue 535_700_954_142_430_953 944_490_975_423_737_791 55_822_386_311_107_416,
    checkpointValue 416_943_982_415_418_776 1_039_258_225_689_091_277 1_193_759_580_477_585_869,
    checkpointValue 193_252_046_913_834_477 727_727_776_063_151_587 2_035_319_666_145_347_949,
    checkpointValue 516_371_078_130_597_771 243_144_708_281_467_858 1_057_517_331_900_427_880,
    checkpointValue 923_426_201_157_464_880 391_290_902_211_496_578 1_452_475_314_094_187_616,
    checkpointValue 639_671_659_020_220_838 409_075_908_364_773_204 1_251_929_112_477_214_610,
    checkpointValue 629_004_106_989_042_882 5_515_601_206_326_830 2_288_051_241_383_542_010,
    checkpointValue 118_501_282_089_005_954 602_296_120_698_837_910 1_732_596_231_505_332_309,
    checkpointValue 750_432_182_062_066_512 680_981_289_943_412_888 441_537_268_433_305_572,
    checkpointValue 783_354_994_741_785_773 584_109_640_261_564_844 1_717_999_980_691_468_860,
    checkpointValue 137_696_721_117_001_077 337_543_822_253_971_250 1_442_730_902_895_491_354,
    checkpointValue 681_126_814_262_244_346 474_437_495_553_984_073 1_081_915_878_719_491_518,
    checkpointValue 402_472_213_180_230_401 925_529_798_315_786_699 562_363_842_124_401_977,
    checkpointValue 62_819_239_127_983_540 604_414_592_228_153_892 34_636_095_681_092_915,
    checkpointValue 549_825_707_308_850_399 945_591_912_654_410_675 972_572_900_140_450_812,
    checkpointValue 374_292_239_582_192_668 993_388_038_144_706_313 619_779_684_053_458_819,
    checkpointValue 672_928_544_341_576_157 332_488_764_002_684_058 39_260_597_874_235_087,
    checkpointValue 31_888_772_549_583_316 537_174_495_628_455_735 417_687_281_909_553_066,
    checkpointValue 1_050_968_472_691_355_934 169_522_546_846_321_948 960_542_270_557_315_004,
    checkpointValue 451_156_377_850_637_781 266_614_449_054_922_116 685_307_793_855_637_260,
    checkpointValue 717_712_821_789_956_376 201_941_832_661_235_807 2_097_774_092_463_517_549,
    checkpointValue 466_024_537_427_575_730 1_009_845_008_047_362_240 1_467_115_628_976_723_719,
    checkpointValue 987_360_131_374_742_770 765_658_094_405_770_457 722_450_833_370_846_338,
    checkpointValue 758_774_347_888_819_855 819_333_593_008_944_894 818_917_633_044_014_089,
    checkpointValue 464_028_846_914_759_355 100_792_919_644_535_265 826_147_020_686_169_002,
    checkpointValue 827_735_882_684_930_668 146_709_578_744_018_131 335_984_033_179_259_153,
    checkpointValue 1_130_633_310_660_104_553 396_217_810_148_187_512 224_186_353_052_591_242,
    checkpointValue 563_573_631_956_401_874 641_924_796_815_188_283 1_388_369_208_232_918_991,
    checkpointValue 631_054_681_440_034_333 1_114_702_584_252_921_158 853_240_304_858_083_629,
    checkpointValue 722_530_571_823_702_015 623_361_081_201_340_070 1_597_018_158_869_012_922,
    checkpointValue 1_033_010_171_298_038_376 196_574_673_185_173_578 1_326_035_118_364_619_214,
    checkpointValue 488_293_527_856_416_212 436_104_558_852_587_163 1_435_560_064_502_289_362,
    checkpointValue 119_823_408_825_104_939 1_144_084_933_761_438_623 1_767_380_551_851_331_617,
    checkpointValue 884_809_592_231_551_085 1_103_890_562_405_060_425 1_540_613_242_422_854_018,
    checkpointValue 1_061_890_578_727_867_496 446_463_296_733_074_148 659_197_469_084_431_438,
    checkpointValue 493_989_658_511_500_782 434_129_616_425_695_908 1_108_091_204_593_767_835,
    checkpointValue 1_122_837_445_187_149_572 989_294_939_583_464_549 588_317_958_244_377_953,
    checkpointValue 483_171_330_327_597_567 838_575_031_304_723_275 2_302_258_935_935_854_798,
    checkpointValue 972_977_937_466_294_177 661_719_465_428_224_317 121_229_145_701_987_905,
    checkpointValue 148_715_853_401_534_886 549_687_498_496_008_180 540_739_169_858_447_407,
    checkpointValue 198_153_389_375_798_358 130_522_608_938_883_106 2_048_490_375_778_536_490,
    checkpointValue 1_113_915_910_451_522_348 1_081_352_575_316_112_569 724_916_339_765_077_765,
    checkpointValue 1_059_595_695_215_886_312 190_737_558_999_978_170 535_580_076_687_495_476,
    checkpointValue 963_726_078_239_940_590 366_391_508_626_707_582 570_941_268_511_766_204,
    checkpointValue 956_548_463_565_780_342 848_140_620_385_163_018 1_401_416_483_385_034_942,
    checkpointValue 1_112_462_754_352_418_321 340_732_685_704_832_245 6_687_592_188_761_991,
    checkpointValue 746_257_469_788_660_218 453_787_020_814_454_530 80_500_642_586_315_912,
    checkpointValue 997_321_653_383_497_993 566_167_472_425_616_708 775_641_477_789_823_028,
    checkpointValue 140_212_240_264_242_198 842_474_720_198_161_739 1_159_428_182_562_304_116,
    checkpointValue 145_036_478_861_997_691 1_028_406_224_626_043_264 2_033_987_411_715_229_752,
    checkpointValue 452_502_240_009_602_331 722_304_425_131_824_275 365_303_557_264_976_689,
    checkpointValue 444_513_576_256_957_171 50_221_982_528_919_847 1_037_439_946_727_737_084,
    checkpointValue 401_906_493_505_828_732 105_933_952_410_009_093 2_101_516_949_792_953_249,
    checkpointValue 1_055_123_727_542_208_371 145_866_692_234_366_151 1_935_065_129_295_620_837,
    checkpointValue 579_710_208_899_795_164 30_491_673_547_575_486 511_521_196_015_684_195,
    checkpointValue 729_535_081_656_038_967 216_954_032_821_015_320 1_622_478_430_303_369_214,
    checkpointValue 658_036_763_090_537_640 1_027_039_798_910_380_372 1_369_659_068_916_896_550,
    checkpointValue 707_078_356_767_331_770 743_244_908_451_123_792 1_048_437_359_544_558_257,
    checkpointValue 778_971_993_240_850_538 78_871_392_870_481_393 1_817_343_800_281_276_044,
    checkpointValue 687_805_633_915_005_142 257_872_085_754_291_692 1_011_674_344_011_023_477,
    checkpointValue 474_000_194_291_158_551 118_577_972_825_222_642 21_913_933_042_451_091,
    checkpointValue 201_066_832_127_980_853 1_115_654_425_997_278_143 566_434_304_137_857_525,
    checkpointValue 1_112_073_096_657_349_706 101_943_159_127_190_247 736_276_878_809_355_635,
    checkpointValue 32_216_312_246_096_399 371_135_052_290_947_270 704_966_896_105_875_228,
    checkpointValue 444_518_406_304_744_304 655_141_523_925_861_734 1_525_150_849_898_598_259,
    checkpointValue 616_011_864_256_194_439 434_063_354_188_799_567 1_957_862_728_082_425_971,
    checkpointValue 229_887_979_518_353_797 331_300_800_273_284_690 930_001_907_510_131_981,
    checkpointValue 79_183_663_951_551_505 1_121_179_363_805_447_655 1_365_098_267_153_706_508,
    checkpointValue 162_452_823_396_811_604 455_115_188_917_345_954 808_161_209_750_435_142,
    checkpointValue 494_294_038_637_544_685 514_769_741_175_259_236 2_156_820_000_887_656_057,
    checkpointValue 6_401_033_110_234_420 605_255_070_590_546_678 959_081_025_837_852_811,
    checkpointValue 812_999_014_855_475_647 1_090_668_866_968_176_772 141_463_680_924_771_637,
    checkpointValue 510_489_582_873_869_221 195_946_562_261_918_201 1_956_985_995_337_902_037,
    checkpointValue 534_563_429_140_343_107 782_586_125_134_744_552 894_844_875_296_022_347]

private abbrev BlockStatement (i : Fin 128) : Prop :=
  CheckpointBlockStatement largePackMatrix checkpointAccumulator i

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock000_015 (offset : Fin 16) :
    BlockStatement (groupIndex 0 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock016_031 (offset : Fin 16) :
    BlockStatement (groupIndex 1 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock032_047 (offset : Fin 16) :
    BlockStatement (groupIndex 2 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock048_063 (offset : Fin 16) :
    BlockStatement (groupIndex 3 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock064_079 (offset : Fin 16) :
    BlockStatement (groupIndex 4 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock080_095 (offset : Fin 16) :
    BlockStatement (groupIndex 5 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock096_111 (offset : Fin 16) :
    BlockStatement (groupIndex 6 offset) := by
  fin_cases offset <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem checkpointBlock112_127 (offset : Fin 16) :
    BlockStatement (groupIndex 7 offset) := by
  fin_cases offset <;> decide +kernel

private theorem checkpointBlockByGroup
    (group : Fin 8) (offset : Fin 16) :
    BlockStatement (groupIndex group offset) := by
  fin_cases group
  · exact checkpointBlock000_015 offset
  · exact checkpointBlock016_031 offset
  · exact checkpointBlock032_047 offset
  · exact checkpointBlock048_063 offset
  · exact checkpointBlock064_079 offset
  · exact checkpointBlock080_095 offset
  · exact checkpointBlock096_111 offset
  · exact checkpointBlock112_127 offset

private theorem checkpointBlocks (i : Fin 128) : BlockStatement i := by
  let group : Fin 8 :=
    ⟨i.val / 16, by
      apply Nat.div_lt_of_lt_mul
      simp [i.isLt]⟩
  let offset : Fin 16 := ⟨i.val % 16, Nat.mod_lt _ (by norm_num)⟩
  have hdecomp : groupIndex group offset = i := by
    apply Fin.ext
    change 16 * (i.val / 16) + i.val % 16 = i.val
    simpa only [Nat.add_comm] using (Nat.mod_add_div i.val 16)
  rw [← hdecomp]
  exact checkpointBlockByGroup group offset

private theorem initialAccumulator :
    (GrayPermanentDP.initialState largePackMatrix).accumulator =
      checkpointAccumulator 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem finalAccumulator :
    checkpointAccumulator ⟨128, by omega⟩ = expectedLargePermanent := by
  rfl

/-- The single three-ring Gray scan. -/
theorem permanent_largePackMatrix :
    Matrix.permanent largePackMatrix = expectedLargePermanent := by
  exact permanent_eq_of_checkpoints largePackMatrix checkpointAccumulator
    expectedLargePermanent initialAccumulator checkpointBlocks finalAccumulator

/-! ## Projection to the three scalar computations -/

def projectLargeA : LargePack →+* LargeResidueA where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def projectLargeB : LargePack →+* LargeResidueB where
  toFun x := x.2.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def projectLargeC : LargePack →+* LargeResidueC where
  toFun x := x.2.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem permanent_map_ringHom
    {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) :
    f (Matrix.permanent M) = Matrix.permanent (M.map f) := by
  classical
  simp only [Matrix.permanent, map_sum, map_prod, Matrix.map_apply]

theorem permanent_largeResidueMatrixA :
    Matrix.permanent largeResidueMatrixA = largePermanentValueA := by
  calc
    Matrix.permanent largeResidueMatrixA =
        Matrix.permanent (largePackMatrix.map projectLargeA) := by
      rfl
    _ = projectLargeA (Matrix.permanent largePackMatrix) :=
      (permanent_map_ringHom projectLargeA largePackMatrix).symm
    _ = projectLargeA expectedLargePermanent := by
      rw [permanent_largePackMatrix]
    _ = largePermanentValueA := rfl

theorem permanent_largeResidueMatrixB :
    Matrix.permanent largeResidueMatrixB = largePermanentValueB := by
  calc
    Matrix.permanent largeResidueMatrixB =
        Matrix.permanent (largePackMatrix.map projectLargeB) := by
      rfl
    _ = projectLargeB (Matrix.permanent largePackMatrix) :=
      (permanent_map_ringHom projectLargeB largePackMatrix).symm
    _ = projectLargeB expectedLargePermanent := by
      rw [permanent_largePackMatrix]
    _ = largePermanentValueB := rfl

theorem permanent_largeResidueMatrixC :
    Matrix.permanent largeResidueMatrixC = largePermanentValueC := by
  calc
    Matrix.permanent largeResidueMatrixC =
        Matrix.permanent (largePackMatrix.map projectLargeC) := by
      rfl
    _ = projectLargeC (Matrix.permanent largePackMatrix) :=
      (permanent_map_ringHom projectLargeC largePackMatrix).symm
    _ = projectLargeC expectedLargePermanent := by
      rw [permanent_largePackMatrix]
    _ = largePermanentValueC := rfl

/-! ## Three independent modular canonical-constant certificates -/

theorem largeCertificateProductA :
    largeGaussValueA * largePermanentValueA =
      largeCertificateResidueA := by
  decide +kernel

theorem largeCertificateProductB :
    largeGaussValueB * largePermanentValueB =
      largeCertificateResidueB := by
  decide +kernel

theorem largeCertificateProductC :
    largeGaussValueC * largePermanentValueC =
      largeCertificateResidueC := by
  decide +kernel

theorem largeCertificateResidueA_eq_integer :
    largeCertificateResidueA =
      (certificateInteger : LargeResidueA) := by
  decide +kernel

theorem largeCertificateResidueB_eq_integer :
    largeCertificateResidueB =
      (certificateInteger : LargeResidueB) := by
  decide +kernel

theorem largeCertificateResidueC_eq_integer :
    largeCertificateResidueC =
      (certificateInteger : LargeResidueC) := by
  decide +kernel

theorem canonicalConstant_mod_largeA :
    (canonicalConstant : LargeResidueA) =
      (certificateInteger : LargeResidueA) :=
  canonicalConstant_mod_of_scalar_certificate
    largeModulusA largeRootA largeRootA_pow_twentyNine
    evalRoot_cyclotomicSum_largeA largeResidueMatrixA scalarMatrix_largeA
    largeGaussValueA largePermanentValueA largeCertificateResidueA
    scalarGauss_largeA permanent_largeResidueMatrixA
    largeCertificateProductA largeCertificateResidueA_eq_integer

theorem canonicalConstant_mod_largeB :
    (canonicalConstant : LargeResidueB) =
      (certificateInteger : LargeResidueB) :=
  canonicalConstant_mod_of_scalar_certificate
    largeModulusB largeRootB largeRootB_pow_twentyNine
    evalRoot_cyclotomicSum_largeB largeResidueMatrixB scalarMatrix_largeB
    largeGaussValueB largePermanentValueB largeCertificateResidueB
    scalarGauss_largeB permanent_largeResidueMatrixB
    largeCertificateProductB largeCertificateResidueB_eq_integer

theorem canonicalConstant_mod_largeC :
    (canonicalConstant : LargeResidueC) =
      (certificateInteger : LargeResidueC) :=
  canonicalConstant_mod_of_scalar_certificate
    largeModulusC largeRootC largeRootC_pow_twentyNine
    evalRoot_cyclotomicSum_largeC largeResidueMatrixC scalarMatrix_largeC
    largeGaussValueC largePermanentValueC largeCertificateResidueC
    scalarGauss_largeC permanent_largeResidueMatrixC
    largeCertificateProductC largeCertificateResidueC_eq_integer

/-! ## Literal coefficients and integral lifting -/

theorem literalCanonicalCoeff_mod_largeA (i : Fin 28) :
    (canonicalCoeff literalCertificateCyclic i : LargeResidueA) =
      if i = 0 then (certificateInteger : LargeResidueA) else 0 := by
  rw [canonicalCoeff_literalCertificateCyclic]
  by_cases hi : i = 0
  · simp [hi, canonicalConstant_mod_largeA]
  · simp [hi]

theorem literalCanonicalCoeff_mod_largeB (i : Fin 28) :
    (canonicalCoeff literalCertificateCyclic i : LargeResidueB) =
      if i = 0 then (certificateInteger : LargeResidueB) else 0 := by
  rw [canonicalCoeff_literalCertificateCyclic]
  by_cases hi : i = 0
  · simp [hi, canonicalConstant_mod_largeB]
  · simp [hi]

theorem literalCanonicalCoeff_mod_largeC (i : Fin 28) :
    (canonicalCoeff literalCertificateCyclic i : LargeResidueC) =
      if i = 0 then (certificateInteger : LargeResidueC) else 0 := by
  rw [canonicalCoeff_literalCertificateCyclic]
  by_cases hi : i = 0
  · simp [hi, canonicalConstant_mod_largeC]
  · simp [hi]

theorem paperCanonicalDifferenceCoeff_mod_largeA (i : Fin 28) :
    (paperCanonicalDifferenceCoeff i : LargeResidueA) = 0 := by
  unfold paperCanonicalDifferenceCoeff
  rw [Int.cast_sub, literalCanonicalCoeff_mod_largeA]
  by_cases hi : i = 0 <;> simp [hi]

theorem paperCanonicalDifferenceCoeff_mod_largeB (i : Fin 28) :
    (paperCanonicalDifferenceCoeff i : LargeResidueB) = 0 := by
  unfold paperCanonicalDifferenceCoeff
  rw [Int.cast_sub, literalCanonicalCoeff_mod_largeB]
  by_cases hi : i = 0 <;> simp [hi]

theorem paperCanonicalDifferenceCoeff_mod_largeC (i : Fin 28) :
    (paperCanonicalDifferenceCoeff i : LargeResidueC) = 0 := by
  unfold paperCanonicalDifferenceCoeff
  rw [Int.cast_sub, literalCanonicalCoeff_mod_largeC]
  by_cases hi : i = 0 <;> simp [hi]

theorem largeModuli_coprimeAB :
    Nat.Coprime largeModulusA largeModulusB := by
  decide +kernel

theorem largeModuli_coprimeAC :
    Nat.Coprime largeModulusA largeModulusC := by
  decide +kernel

theorem largeModuli_coprimeBC :
    Nat.Coprime largeModulusB largeModulusC := by
  decide +kernel

def largeModulusProduct : ℤ :=
  (largeModulusA : ℤ) * largeModulusB * largeModulusC

theorem largeModulusProduct_eq :
    largeModulusProduct =
      3_075_545_109_364_976_900_170_809_219_633_766_916_597_396_858_594_131_937 := by
  norm_num [largeModulusProduct, largeModulusA, largeModulusB,
    largeModulusC, paperModulus2]

theorem largeModulusProduct_gt_twice_bound :
    largeModulusProduct > 2 * (paperBoundB + paperBoundE) := by
  norm_num [largeModulusProduct, largeModulusA, largeModulusB,
    largeModulusC, paperModulus2, paperBoundB, paperBoundE,
    Nat.factorial]

/-- The literal coefficientwise equation lifted over `ℤ` from the three
independent scalar computations. -/
theorem paperCanonicalDifferenceCoeff_eq_zero (i : Fin 28) :
    paperCanonicalDifferenceCoeff i = 0 := by
  apply CyclotomicLifting.eq_zero_of_three_zmod
    largeModulusA largeModulusB largeModulusC paperBoundB paperBoundE
      (paperCanonicalDifferenceCoeff i)
  · exact largeModuli_coprimeAB
  · exact largeModuli_coprimeAC
  · exact largeModuli_coprimeBC
  · exact paperCanonicalDifferenceCoeff_mod_largeA i
  · exact paperCanonicalDifferenceCoeff_mod_largeB i
  · exact paperCanonicalDifferenceCoeff_mod_largeC i
  · exact CyclotomicLifting.paperCanonicalDifferenceCoeff_abs_le i
  · simpa [largeModulusProduct] using
      largeModulusProduct_gt_twice_bound

theorem paperCanonicalDifferenceCoeff_all_eq_zero :
    ∀ i : Fin 28, paperCanonicalDifferenceCoeff i = 0 :=
  paperCanonicalDifferenceCoeff_eq_zero

/-- The independent three-scalar route determines the integral canonical
constant without invoking the six-small-modulus CRT. -/
theorem canonicalConstant_eq_certificateInteger :
    canonicalConstant = certificateInteger := by
  have hzero := paperCanonicalDifferenceCoeff_eq_zero (0 : Fin 28)
  unfold paperCanonicalDifferenceCoeff at hzero
  rw [canonicalCoeff_literalCertificateCyclic] at hzero
  have hsub : canonicalConstant - certificateInteger = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

theorem literalCanonicalCoefficients_exact (i : Fin 28) :
    canonicalCoeff literalCertificateCyclic i =
      if i = 0 then certificateInteger else 0 :=
  canonicalCoeff_literalCertificateCyclic_of_canonicalConstant
    canonicalConstant_eq_certificateInteger i

/-- Unconditional literal cyclic-ring form of equation (4.1). -/
theorem literal_equation_four_one :
    literalQuotientGauss * Matrix.permanent literalQuotientMatrix =
      (certificateInteger : CyclotomicRing) :=
  literal_ring_certificate_of_canonicalConstant
    canonicalConstant_eq_certificateInteger

/-- Unconditional polynomial-quotient form of equation (4.1). -/
theorem polynomial_equation_four_one :
    PolynomialQuotientCertificate.sectionFourGauss *
        Matrix.permanent PolynomialQuotientCertificate.sectionFourMatrix =
      (certificateInteger :
        PolynomialQuotientCertificate.PolynomialCyclotomicRing) :=
  PolynomialQuotientCertificate.equation_four_one_of_canonicalConstant
    canonicalConstant_eq_certificateInteger

/-! ## A second exact analytic endgame -/

/-- Exact cotangent-permanent value obtained through this independent
three-scalar certificate. -/
theorem real_cotangentPermanent29_value_threeScalar :
    Real.sqrt 29 * realCotMatrix29.permanent = 84643985981440 := by
  apply real_cotangentPermanent29_value_of_certificate
  exact CertificateComplexBridge.complex_certificate_of_canonicalConstant
    canonicalConstant_eq_certificateInteger

theorem legendreSym_neg_one_twentyNine_threeScalar :
    legendreSym 29 (-1) = 1 := by
  rw [legendreSym.at_neg_one (by norm_num)]
  norm_num [ZMod.χ₄_nat_eq_if_mod_four]

/-- The sign counterexample, with this module as its finite-certificate
dependency rather than the six-small-modulus route. -/
theorem sun_cotangent_sign_counterexample_threeScalar :
    (legendreSym 29 (-1) : ℝ) *
        (Real.sqrt 29 * realCotMatrix29.permanent) > 0 := by
  rw [legendreSym_neg_one_twentyNine_threeScalar]
  norm_num [real_cotangentPermanent29_value_threeScalar]

end ThreeScalarCyclotomicCertificate
end SunCotangent
