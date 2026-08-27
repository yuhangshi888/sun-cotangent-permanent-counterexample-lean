import SunCotangent.ScalarSpecialization

/-!
# Finite-ring certificates for the cyclotomic identity

This module is deliberately separate from the symbolic cyclotomic core.  Its
closed computations may be checked independently without making every import
of the group-ring argument normalize the modular permanent.
-/

open scoped BigOperators

namespace SunCotangent
namespace CyclotomicCertificate

noncomputable section

/-! ## First modulus

The other five moduli use the same declarations and will be combined in one
product-ring computation rather than six duplicated kernel reductions.
-/

def q1 : ℕ := 1_999_998_457
def w1 : ZMod q1 := 929_222_705
def gaussValue1 : ZMod q1 := 1_391_190_231
def permanentValue1 : ZMod q1 := 96_850_916
def certificateResidue1 : ZMod q1 := 153_085_864

def entryTable1 : Z29 → ZMod q1 :=
  ![0, 1_998_685_368, 318_853_920, 1_722_124_876, 1_401_018_914,
    274_672_408, 1_588_960_226, 1_630_493_704, 516_119_317, 716_931_661,
    1_116_679_129, 1_471_730_046, 829_759_191, 452_865_635, 942_671_461,
    1_057_326_996, 1_547_132_822, 1_170_239_266, 528_268_411, 883_319_328,
    1_283_066_796, 1_483_879_140, 369_504_753, 411_038_231, 1_725_326_049,
    598_979_543, 277_873_581, 1_681_144_537, 1_313_089]

def residueMatrix1 : Matrix (Fin 14) (Fin 14) (ZMod q1) :=
  fun i j ↦ entryTable1
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem root1 : w1 ^ 29 = 1 := by decide +kernel

theorem cyclotomicPowerSum1 : ∑ e : Z29, w1 ^ e.val = 0 := by
  decide +kernel

theorem evalRoot_cyclotomicSum1 :
    evalRoot q1 w1 root1 cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero q1 w1 root1 cyclotomicPowerSum1

theorem entryTable1_correct : ∀ e : Z29,
    entryTable1 e = scalarEntry q1 w1 e := by
  decide +kernel

theorem gauss1 : scalarGauss q1 w1 = 1_391_190_231 := by
  decide +kernel

theorem scalarMatrix1_eq_residueMatrix1 :
    scalarMatrix q1 w1 = residueMatrix1 := by
  ext i j
  simp only [scalarMatrix, residueMatrix1]
  exact (entryTable1_correct _).symm

theorem certificateProduct1 :
    gaussValue1 * permanentValue1 = certificateResidue1 := by
  decide +kernel

theorem certificateResidue1_eq_integer :
    certificateResidue1 = (certificateInteger : ZMod q1) := by
  decide +kernel

theorem canonicalConstant_mod1_of_permanent
    (hpermanent : Matrix.permanent residueMatrix1 = permanentValue1) :
    (canonicalConstant : ZMod q1) = (certificateInteger : ZMod q1) :=
  canonicalConstant_mod_of_scalar_certificate q1 w1 root1
    evalRoot_cyclotomicSum1 residueMatrix1 scalarMatrix1_eq_residueMatrix1
    gaussValue1 permanentValue1 certificateResidue1 gauss1 hpermanent
    certificateProduct1 certificateResidue1_eq_integer

/-! ## Second modulus -/

def q2 : ℕ := 1_999_997_413
def w2 : ZMod q2 := 1_260_875_631
def gaussValue2 : ZMod q2 := 106_827_755
def permanentValue2 : ZMod q2 := 483_797_571
def certificateResidue2 : ZMod q2 := 1_236_439_324

def entryTable2 : Z29 → ZMod q2 :=
  ![0, 314_245_547, 1_930_870_476, 1_185_120_526, 502_293_618,
    476_657_792, 784_699_094, 423_761_663, 263_842_799, 155_111_807,
    1_831_320_299, 1_914_629_877, 934_676_143, 1_513_473_389, 254_063_177,
    1_745_934_236, 486_524_024, 1_065_321_270, 85_367_536, 168_677_114,
    1_844_885_606, 1_736_154_614, 1_576_235_750, 1_215_298_319,
    1_523_339_621, 1_497_703_795, 814_876_887, 69_126_937, 1_685_751_866]

def residueMatrix2 : Matrix (Fin 14) (Fin 14) (ZMod q2) :=
  fun i j ↦ entryTable2
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem root2 : w2 ^ 29 = 1 := by decide +kernel

theorem cyclotomicPowerSum2 : ∑ e : Z29, w2 ^ e.val = 0 := by
  decide +kernel

theorem evalRoot_cyclotomicSum2 :
    evalRoot q2 w2 root2 cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero q2 w2 root2 cyclotomicPowerSum2

theorem entryTable2_correct : ∀ e : Z29,
    entryTable2 e = scalarEntry q2 w2 e := by
  decide +kernel

theorem gauss2 : scalarGauss q2 w2 = gaussValue2 := by
  decide +kernel

theorem scalarMatrix2_eq_residueMatrix2 :
    scalarMatrix q2 w2 = residueMatrix2 := by
  ext i j
  simp only [scalarMatrix, residueMatrix2]
  exact (entryTable2_correct _).symm

theorem certificateProduct2 :
    gaussValue2 * permanentValue2 = certificateResidue2 := by
  decide +kernel

theorem certificateResidue2_eq_integer :
    certificateResidue2 = (certificateInteger : ZMod q2) := by
  decide +kernel

theorem canonicalConstant_mod2_of_permanent
    (hpermanent : Matrix.permanent residueMatrix2 = permanentValue2) :
    (canonicalConstant : ZMod q2) = (certificateInteger : ZMod q2) :=
  canonicalConstant_mod_of_scalar_certificate q2 w2 root2
    evalRoot_cyclotomicSum2 residueMatrix2 scalarMatrix2_eq_residueMatrix2
    gaussValue2 permanentValue2 certificateResidue2 gauss2 hpermanent
    certificateProduct2 certificateResidue2_eq_integer

/-! ## Third modulus -/

def q3 : ℕ := 1_999_996_949
def w3 : ZMod q3 := 1_074_338_178
def gaussValue3 : ZMod q3 := 1_918_644_949
def permanentValue3 : ZMod q3 := 693_584_846
def certificateResidue3 : ZMod q3 := 1_532_477_649

def entryTable3 : Z29 → ZMod q3 :=
  ![0, 1_113_673_368, 1_534_958_633, 1_194_397_836, 1_921_640_141,
    444_990_050, 1_124_041_784, 1_114_169_330, 831_810_788, 727_540_974,
    1_140_142_213, 1_764_399_574, 352_692_106, 189_450_300, 556_253_815,
    1_443_743_134, 1_810_546_649, 1_647_304_843, 235_597_375, 859_854_736,
    1_272_455_975, 1_168_186_161, 885_827_619, 875_955_165,
    1_555_006_899, 78_356_808, 805_599_113, 465_038_316, 886_323_581]

def residueMatrix3 : Matrix (Fin 14) (Fin 14) (ZMod q3) :=
  fun i j ↦ entryTable3
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem root3 : w3 ^ 29 = 1 := by decide +kernel

theorem cyclotomicPowerSum3 : ∑ e : Z29, w3 ^ e.val = 0 := by
  decide +kernel

theorem evalRoot_cyclotomicSum3 :
    evalRoot q3 w3 root3 cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero q3 w3 root3 cyclotomicPowerSum3

theorem entryTable3_correct : ∀ e : Z29,
    entryTable3 e = scalarEntry q3 w3 e := by
  decide +kernel

theorem gauss3 : scalarGauss q3 w3 = gaussValue3 := by
  decide +kernel

theorem scalarMatrix3_eq_residueMatrix3 :
    scalarMatrix q3 w3 = residueMatrix3 := by
  ext i j
  simp only [scalarMatrix, residueMatrix3]
  exact (entryTable3_correct _).symm

theorem certificateProduct3 :
    gaussValue3 * permanentValue3 = certificateResidue3 := by
  decide +kernel

theorem certificateResidue3_eq_integer :
    certificateResidue3 = (certificateInteger : ZMod q3) := by
  decide +kernel

theorem canonicalConstant_mod3_of_permanent
    (hpermanent : Matrix.permanent residueMatrix3 = permanentValue3) :
    (canonicalConstant : ZMod q3) = (certificateInteger : ZMod q3) :=
  canonicalConstant_mod_of_scalar_certificate q3 w3 root3
    evalRoot_cyclotomicSum3 residueMatrix3 scalarMatrix3_eq_residueMatrix3
    gaussValue3 permanentValue3 certificateResidue3 gauss3 hpermanent
    certificateProduct3 certificateResidue3_eq_integer

/-! ## Fourth modulus -/

def q4 : ℕ := 1_999_996_253
def w4 : ZMod q4 := 1_150_657_067
def gaussValue4 : ZMod q4 := 1_553_055_020
def permanentValue4 : ZMod q4 := 716_813_256
def certificateResidue4 : ZMod q4 := 1_311_922_605

def entryTable4 : Z29 → ZMod q4 :=
  ![0, 273_384_967, 780_004_793, 208_427_548, 678_251_757, 1_679_869_524,
    381_415_014, 1_037_437_018, 1_162_119_595, 1_023_539_539, 218_390_023,
    1_656_450_335, 1_361_513_621, 1_052_581_063, 1_453_223_700,
    546_772_553, 947_415_190, 638_482_632, 343_545_918, 1_781_606_230,
    976_456_714, 837_876_658, 962_559_235, 1_618_581_239, 320_126_729,
    1_321_744_496, 1_791_568_705, 1_219_991_460, 1_726_611_286]

def residueMatrix4 : Matrix (Fin 14) (Fin 14) (ZMod q4) :=
  fun i j ↦ entryTable4
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem root4 : w4 ^ 29 = 1 := by decide +kernel

theorem cyclotomicPowerSum4 : ∑ e : Z29, w4 ^ e.val = 0 := by
  decide +kernel

theorem evalRoot_cyclotomicSum4 :
    evalRoot q4 w4 root4 cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero q4 w4 root4 cyclotomicPowerSum4

theorem entryTable4_correct : ∀ e : Z29,
    entryTable4 e = scalarEntry q4 w4 e := by
  decide +kernel

theorem gauss4 : scalarGauss q4 w4 = gaussValue4 := by
  decide +kernel

theorem scalarMatrix4_eq_residueMatrix4 :
    scalarMatrix q4 w4 = residueMatrix4 := by
  ext i j
  simp only [scalarMatrix, residueMatrix4]
  exact (entryTable4_correct _).symm

theorem certificateProduct4 :
    gaussValue4 * permanentValue4 = certificateResidue4 := by
  decide +kernel

theorem certificateResidue4_eq_integer :
    certificateResidue4 = (certificateInteger : ZMod q4) := by
  decide +kernel

theorem canonicalConstant_mod4_of_permanent
    (hpermanent : Matrix.permanent residueMatrix4 = permanentValue4) :
    (canonicalConstant : ZMod q4) = (certificateInteger : ZMod q4) :=
  canonicalConstant_mod_of_scalar_certificate q4 w4 root4
    evalRoot_cyclotomicSum4 residueMatrix4 scalarMatrix4_eq_residueMatrix4
    gaussValue4 permanentValue4 certificateResidue4 gauss4 hpermanent
    certificateProduct4 certificateResidue4_eq_integer

/-! ## Fifth modulus -/

def q5 : ℕ := 1_999_996_021
def w5 : ZMod q5 := 1_809_056_026
def gaussValue5 : ZMod q5 := 176_050_613
def permanentValue5 : ZMod q5 := 1_803_435_822
def certificateResidue5 : ZMod q5 := 1_628_768_460

def entryTable5 : Z29 → ZMod q5 :=
  ![0, 196_682_935, 421_194_783, 672_935_132, 1_769_744_361, 885_167_526,
    209_509_161, 616_648_248, 1_505_199_334, 41_035_376, 1_125_915_234,
    806_847_302, 1_857_104_329, 235_178_383, 698_660_412, 1_301_335_609,
    1_764_817_638, 142_891_692, 1_193_148_719, 874_080_787, 1_958_960_645,
    494_796_687, 1_383_347_773, 1_790_486_860, 1_114_828_495, 230_251_660,
    1_327_060_889, 1_578_801_238, 1_803_313_086]

def residueMatrix5 : Matrix (Fin 14) (Fin 14) (ZMod q5) :=
  fun i j ↦ entryTable5
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem root5 : w5 ^ 29 = 1 := by decide +kernel

theorem cyclotomicPowerSum5 : ∑ e : Z29, w5 ^ e.val = 0 := by
  decide +kernel

theorem evalRoot_cyclotomicSum5 :
    evalRoot q5 w5 root5 cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero q5 w5 root5 cyclotomicPowerSum5

theorem entryTable5_correct : ∀ e : Z29,
    entryTable5 e = scalarEntry q5 w5 e := by
  decide +kernel

theorem gauss5 : scalarGauss q5 w5 = gaussValue5 := by
  decide +kernel

theorem scalarMatrix5_eq_residueMatrix5 :
    scalarMatrix q5 w5 = residueMatrix5 := by
  ext i j
  simp only [scalarMatrix, residueMatrix5]
  exact (entryTable5_correct _).symm

theorem certificateProduct5 :
    gaussValue5 * permanentValue5 = certificateResidue5 := by
  decide +kernel

theorem certificateResidue5_eq_integer :
    certificateResidue5 = (certificateInteger : ZMod q5) := by
  decide +kernel

theorem canonicalConstant_mod5_of_permanent
    (hpermanent : Matrix.permanent residueMatrix5 = permanentValue5) :
    (canonicalConstant : ZMod q5) = (certificateInteger : ZMod q5) :=
  canonicalConstant_mod_of_scalar_certificate q5 w5 root5
    evalRoot_cyclotomicSum5 residueMatrix5 scalarMatrix5_eq_residueMatrix5
    gaussValue5 permanentValue5 certificateResidue5 gauss5 hpermanent
    certificateProduct5 certificateResidue5_eq_integer

/-! ## Sixth modulus -/

def q6 : ℕ := 1_999_993_469
def w6 : ZMod q6 := 782_146_401
def gaussValue6 : ZMod q6 := 1_267_707_994
def permanentValue6 : ZMod q6 := 1_755_245_617
def certificateResidue6 : ZMod q6 := 319_167_371

def entryTable6 : Z29 → ZMod q6 :=
  ![0, 1_801_452_078, 1_080_027_859, 986_165_414, 1_933_641_646,
    886_598_291, 1_836_755_013, 559_750_518, 1_056_840_859, 1_405_752_474,
    589_197_863, 1_941_565_770, 1_930_672_461, 876_819_485, 106_971_378,
    1_893_022_091, 1_123_173_984, 69_321_008, 58_427_699, 1_410_795_606,
    594_240_995, 943_152_610, 1_440_242_951, 163_238_456, 1_113_395_178,
    66_351_823, 1_013_828_055, 919_965_610, 198_541_391]

def residueMatrix6 : Matrix (Fin 14) (Fin 14) (ZMod q6) :=
  fun i j ↦ entryTable6
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem root6 : w6 ^ 29 = 1 := by decide +kernel

theorem cyclotomicPowerSum6 : ∑ e : Z29, w6 ^ e.val = 0 := by
  decide +kernel

theorem evalRoot_cyclotomicSum6 :
    evalRoot q6 w6 root6 cyclotomicSum = 0 :=
  evalRoot_cyclotomicSum_eq_zero q6 w6 root6 cyclotomicPowerSum6

theorem entryTable6_correct : ∀ e : Z29,
    entryTable6 e = scalarEntry q6 w6 e := by
  decide +kernel

theorem gauss6 : scalarGauss q6 w6 = gaussValue6 := by
  decide +kernel

theorem scalarMatrix6_eq_residueMatrix6 :
    scalarMatrix q6 w6 = residueMatrix6 := by
  ext i j
  simp only [scalarMatrix, residueMatrix6]
  exact (entryTable6_correct _).symm

theorem certificateProduct6 :
    gaussValue6 * permanentValue6 = certificateResidue6 := by
  decide +kernel

theorem certificateResidue6_eq_integer :
    certificateResidue6 = (certificateInteger : ZMod q6) := by
  decide +kernel

theorem canonicalConstant_mod6_of_permanent
    (hpermanent : Matrix.permanent residueMatrix6 = permanentValue6) :
    (canonicalConstant : ZMod q6) = (certificateInteger : ZMod q6) :=
  canonicalConstant_mod_of_scalar_certificate q6 w6 root6
    evalRoot_cyclotomicSum6 residueMatrix6 scalarMatrix6_eq_residueMatrix6
    gaussValue6 permanentValue6 certificateResidue6 gauss6 hpermanent
    certificateProduct6 certificateResidue6_eq_integer

/-! ## One six-component permanent computation

The six residue rings are packaged as a dependent function ring.  Arithmetic
is componentwise, so one execution of a generic permanent evaluator on
`packMatrix` computes all six residues while its correctness theorem remains
the ordinary ring-generic permanent theorem.
-/

def packedModulus : Fin 6 → ℕ :=
  ![q1, q2, q3, q4, q5, q6]

abbrev ModPack := (i : Fin 6) → ZMod (packedModulus i)

def rootPack : ModPack
  | 0 => w1
  | 1 => w2
  | 2 => w3
  | 3 => w4
  | 4 => w5
  | 5 => w6

def expectedPermanentPack : ModPack
  | 0 => permanentValue1
  | 1 => permanentValue2
  | 2 => permanentValue3
  | 3 => permanentValue4
  | 4 => permanentValue5
  | 5 => permanentValue6

def expectedCertificatePack : ModPack
  | 0 => certificateResidue1
  | 1 => certificateResidue2
  | 2 => certificateResidue3
  | 3 => certificateResidue4
  | 4 => certificateResidue5
  | 5 => certificateResidue6

def packMatrix (i j : Fin 14) : ModPack
  | 0 => residueMatrix1 i j
  | 1 => residueMatrix2 i j
  | 2 => residueMatrix3 i j
  | 3 => residueMatrix4 i j
  | 4 => residueMatrix5 i j
  | 5 => residueMatrix6 i j

private theorem permanent_modPack_apply
    (M : Matrix (Fin 14) (Fin 14) ModPack) (k : Fin 6) :
    Matrix.permanent M k =
      Matrix.permanent (fun i j ↦ M i j k) := by
  classical
  simp only [Matrix.permanent, Finset.sum_apply, Finset.prod_apply]

theorem permanent1_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent residueMatrix1 = permanentValue1 := by
  have h := congrFun hpack (0 : Fin 6)
  rw [permanent_modPack_apply] at h
  exact h

theorem permanent2_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent residueMatrix2 = permanentValue2 := by
  have h := congrFun hpack (1 : Fin 6)
  rw [permanent_modPack_apply] at h
  exact h

theorem permanent3_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent residueMatrix3 = permanentValue3 := by
  have h := congrFun hpack (2 : Fin 6)
  rw [permanent_modPack_apply] at h
  exact h

theorem permanent4_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent residueMatrix4 = permanentValue4 := by
  have h := congrFun hpack (3 : Fin 6)
  rw [permanent_modPack_apply] at h
  exact h

theorem permanent5_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent residueMatrix5 = permanentValue5 := by
  have h := congrFun hpack (4 : Fin 6)
  rw [permanent_modPack_apply] at h
  exact h

theorem permanent6_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent residueMatrix6 = permanentValue6 := by
  have h := congrFun hpack (5 : Fin 6)
  rw [permanent_modPack_apply] at h
  exact h

/-
The Gray-code evaluator will discharge exactly one closed theorem:

  Matrix.permanent packMatrix = expectedPermanentPack.

Its executable equality is kept out until the evaluator module exports its
final proved interface; no component permanent is recomputed here.
-/

end
end CyclotomicCertificate
end SunCotangent
