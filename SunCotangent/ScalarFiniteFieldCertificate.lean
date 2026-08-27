import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import SunCotangent.ModularCertificates

/-!
# The three literal finite-field certificates from Section 3

This file spells out the three rows of Table 1 using the literal quotient

`(w^e + 1) / (w^e - 1)`.

The permanent computation itself deliberately remains an explicit hypothesis.
The checkpoint evaluator can later supply either the three hypotheses or the
single packed hypothesis, without making this structural file import or rerun
the long computation.

No integrality theorem for Sun's analytic quantity is assumed here.  The final
CRT theorem has an explicit integer parameter and explicit specialization
hypotheses; applying it to `t'_29` requires a separate proof that `t'_29` is
that integer.
-/

open scoped BigOperators

namespace SunCotangent
namespace ScalarFiniteFieldCertificate

open CyclotomicCertificate

local instance primeFact29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-! ## The three primes and their primitive twenty-ninth roots -/

theorem q1_prime : Nat.Prime q1 := by
  norm_num [q1]

theorem q2_prime : Nat.Prime q2 := by
  norm_num [q2]

theorem q3_prime : Nat.Prime q3 := by
  norm_num [q3]

local instance q1PrimeFact : Fact (Nat.Prime q1) := ⟨q1_prime⟩
local instance q2PrimeFact : Fact (Nat.Prime q2) := ⟨q2_prime⟩
local instance q3PrimeFact : Fact (Nat.Prime q3) := ⟨q3_prime⟩

theorem q1_mod_116 : q1 ≡ 1 [MOD 116] := by
  norm_num [Nat.ModEq, q1]

theorem q2_mod_116 : q2 ≡ 1 [MOD 116] := by
  norm_num [Nat.ModEq, q2]

theorem q3_mod_116 : q3 ≡ 1 [MOD 116] := by
  norm_num [Nat.ModEq, q3]

theorem w1_eq_two_pow :
    w1 = (2 : ZMod q1) ^ ((q1 - 1) / 29) := by
  unfold w1 q1
  reduce_mod_char

theorem w2_eq_two_pow :
    w2 = (2 : ZMod q2) ^ ((q2 - 1) / 29) := by
  unfold w2 q2
  reduce_mod_char

theorem w3_eq_two_pow :
    w3 = (2 : ZMod q3) ^ ((q3 - 1) / 29) := by
  unfold w3 q3
  reduce_mod_char

theorem w1_ne_one : w1 ≠ 1 := by
  unfold w1 q1
  reduce_mod_char
  decide +kernel

theorem w2_ne_one : w2 ≠ 1 := by
  unfold w2 q2
  reduce_mod_char
  decide +kernel

theorem w3_ne_one : w3 ≠ 1 := by
  unfold w3 q3
  reduce_mod_char
  decide +kernel

/-- The first displayed root has multiplicative order exactly `29`. -/
theorem w1_order : orderOf w1 = 29 :=
  orderOf_eq_prime root1 w1_ne_one

/-- The second displayed root has multiplicative order exactly `29`. -/
theorem w2_order : orderOf w2 = 29 :=
  orderOf_eq_prime root2 w2_ne_one

/-- The third displayed root has multiplicative order exactly `29`. -/
theorem w3_order : orderOf w3 = 29 :=
  orderOf_eq_prime root3 w3_ne_one

/-! ## Literal quotient entries and nonvanishing denominators -/

/-- The literal entry `(w^e + 1) / (w^e - 1)` used in Section 3.  Its value
at `e = 0` is irrelevant: every exponent occurring in the matrix is nonzero. -/
def literalREntry (q : ℕ) [Fact (Nat.Prime q)]
    (w : ZMod q) (e : Z29) : ZMod q :=
  (w ^ e.val + 1) / (w ^ e.val - 1)

/-- The literal `14 x 14` matrix `R_q` from Section 3. -/
def literalRMatrix (q : ℕ) [Fact (Nat.Prime q)] (w : ZMod q) :
    Matrix (Fin 14) (Fin 14) (ZMod q) :=
  fun i j ↦ literalREntry q w
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

/-- No exponent appearing in `R_q` is zero modulo `29`. -/
theorem literalRMatrix_exponent_ne_zero (i j : Fin 14) :
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29)) ≠ 0 := by
  revert i j
  decide +kernel

private theorem denominator_ne_zero_of_order_twentyNine
    {q : ℕ} (w : ZMod q) (hw : orderOf w = 29)
    (e : Z29) (he : e ≠ 0) :
    w ^ e.val - 1 ≠ 0 := by
  intro hzero
  have hpow : w ^ e.val = 1 := sub_eq_zero.mp hzero
  have hdvd : 29 ∣ e.val := by
    have hdvdOrder : orderOf w ∣ e.val :=
      (orderOf_dvd_iff_pow_eq_one).2 hpow
    simpa only [hw] using hdvdOrder
  have hval : e.val = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd e.val_lt
  exact he ((ZMod.val_eq_zero e).mp hval)

theorem denominator1_nonzero (e : Z29) (he : e ≠ 0) :
    w1 ^ e.val - 1 ≠ 0 :=
  denominator_ne_zero_of_order_twentyNine w1 w1_order e he

theorem denominator2_nonzero (e : Z29) (he : e ≠ 0) :
    w2 ^ e.val - 1 ≠ 0 :=
  denominator_ne_zero_of_order_twentyNine w2 w2_order e he

theorem denominator3_nonzero (e : Z29) (he : e ≠ 0) :
    w3 ^ e.val - 1 ≠ 0 :=
  denominator_ne_zero_of_order_twentyNine w3 w3_order e he

theorem literalRMatrix1_denominator_nonzero (i j : Fin 14) :
    w1 ^ ((((i.val + 1 : ℕ) : Z29) *
      ((j.val + 1 : ℕ) : Z29)).val) - 1 ≠ 0 :=
  denominator1_nonzero _ (literalRMatrix_exponent_ne_zero i j)

theorem literalRMatrix2_denominator_nonzero (i j : Fin 14) :
    w2 ^ ((((i.val + 1 : ℕ) : Z29) *
      ((j.val + 1 : ℕ) : Z29)).val) - 1 ≠ 0 :=
  denominator2_nonzero _ (literalRMatrix_exponent_ne_zero i j)

theorem literalRMatrix3_denominator_nonzero (i j : Fin 14) :
    w3 ^ ((((i.val + 1 : ℕ) : Z29) *
      ((j.val + 1 : ℕ) : Z29)).val) - 1 ≠ 0 :=
  denominator3_nonzero _ (literalRMatrix_exponent_ne_zero i j)

/-! ## The literal Gauss sums -/

/-- The displayed finite-field Gauss sum.  The zero term is harmless because
`quadraticChar29 0 = 0`. -/
def literalGauss (q : ℕ) (w : ZMod q) : ZMod q :=
  ∑ e : Z29, (quadraticChar29 e : ZMod q) * w ^ e.val

theorem literalGauss_eq_scalarGauss (q : ℕ) (w : ZMod q) :
    literalGauss q w = scalarGauss q w := rfl

theorem literalGauss1_value :
    literalGauss q1 w1 = (1_391_190_231 : ZMod q1) := by
  change scalarGauss q1 w1 = (1_391_190_231 : ZMod q1)
  exact gauss1

theorem literalGauss2_value :
    literalGauss q2 w2 = (106_827_755 : ZMod q2) := by
  change scalarGauss q2 w2 = (106_827_755 : ZMod q2)
  exact gauss2

theorem literalGauss3_value :
    literalGauss q3 w3 = (1_918_644_949 : ZMod q3) := by
  change scalarGauss q3 w3 = (1_918_644_949 : ZMod q3)
  exact gauss3

theorem literalGauss1_sq : literalGauss q1 w1 ^ 2 = (29 : ZMod q1) := by
  rw [literalGauss1_value]
  unfold q1
  reduce_mod_char

theorem literalGauss2_sq : literalGauss q2 w2 ^ 2 = (29 : ZMod q2) := by
  rw [literalGauss2_value]
  unfold q2
  reduce_mod_char

theorem literalGauss3_sq : literalGauss q3 w3 ^ 2 = (29 : ZMod q3) := by
  rw [literalGauss3_value]
  unfold q3
  reduce_mod_char

/-! ## Transport from the integral tables to the literal matrices -/

/-- The first existing entry table is exactly `29` times the literal quotient
table. -/
theorem entryTable1_eq_scaled_literalR : ∀ e : Z29,
    entryTable1 e = (29 : ZMod q1) * literalREntry q1 w1 e := by
  decide +kernel

/-- The second existing entry table is exactly `29` times the literal quotient
table. -/
theorem entryTable2_eq_scaled_literalR : ∀ e : Z29,
    entryTable2 e = (29 : ZMod q2) * literalREntry q2 w2 e := by
  decide +kernel

/-- The third existing entry table is exactly `29` times the literal quotient
table. -/
theorem entryTable3_eq_scaled_literalR : ∀ e : Z29,
    entryTable3 e = (29 : ZMod q3) * literalREntry q3 w3 e := by
  decide +kernel

theorem residueMatrix1_eq_scaled_literalR :
    residueMatrix1 = (29 : ZMod q1) • literalRMatrix q1 w1 := by
  ext i j
  change entryTable1 _ = (29 : ZMod q1) * literalREntry q1 w1 _
  exact entryTable1_eq_scaled_literalR _

theorem residueMatrix2_eq_scaled_literalR :
    residueMatrix2 = (29 : ZMod q2) • literalRMatrix q2 w2 := by
  ext i j
  change entryTable2 _ = (29 : ZMod q2) * literalREntry q2 w2 _
  exact entryTable2_eq_scaled_literalR _

theorem residueMatrix3_eq_scaled_literalR :
    residueMatrix3 = (29 : ZMod q3) • literalRMatrix q3 w3 := by
  ext i j
  change entryTable3 _ = (29 : ZMod q3) * literalREntry q3 w3 _
  exact entryTable3_eq_scaled_literalR _

/-- Table 1, first permanent row, transported from the already-scaled
permanent certificate. -/
theorem table1_permanent_q1_of_scaled
    (hscaled : Matrix.permanent residueMatrix1 = permanentValue1) :
    Matrix.permanent (literalRMatrix q1 w1) =
      (1_767_907_462 : ZMod q1) := by
  have h29pow : (29 : ZMod q1) ^ 14 ≠ 0 := by
    unfold q1
    reduce_mod_char
    decide +kernel
  apply mul_left_cancel₀ h29pow
  calc
    (29 : ZMod q1) ^ 14 * Matrix.permanent (literalRMatrix q1 w1) =
        Matrix.permanent ((29 : ZMod q1) • literalRMatrix q1 w1) := by
      rw [Matrix.permanent_smul, Fintype.card_fin]
    _ = Matrix.permanent residueMatrix1 := by
      rw [← residueMatrix1_eq_scaled_literalR]
    _ = permanentValue1 := hscaled
    _ = (29 : ZMod q1) ^ 14 * (1_767_907_462 : ZMod q1) := by
      unfold permanentValue1 q1
      reduce_mod_char

/-- Table 1, second permanent row, transported from the already-scaled
permanent certificate. -/
theorem table1_permanent_q2_of_scaled
    (hscaled : Matrix.permanent residueMatrix2 = permanentValue2) :
    Matrix.permanent (literalRMatrix q2 w2) =
      (1_110_131_281 : ZMod q2) := by
  have h29pow : (29 : ZMod q2) ^ 14 ≠ 0 := by
    unfold q2
    reduce_mod_char
    decide +kernel
  apply mul_left_cancel₀ h29pow
  calc
    (29 : ZMod q2) ^ 14 * Matrix.permanent (literalRMatrix q2 w2) =
        Matrix.permanent ((29 : ZMod q2) • literalRMatrix q2 w2) := by
      rw [Matrix.permanent_smul, Fintype.card_fin]
    _ = Matrix.permanent residueMatrix2 := by
      rw [← residueMatrix2_eq_scaled_literalR]
    _ = permanentValue2 := hscaled
    _ = (29 : ZMod q2) ^ 14 * (1_110_131_281 : ZMod q2) := by
      unfold permanentValue2 q2
      reduce_mod_char

/-- Table 1, third permanent row, transported from the already-scaled
permanent certificate. -/
theorem table1_permanent_q3_of_scaled
    (hscaled : Matrix.permanent residueMatrix3 = permanentValue3) :
    Matrix.permanent (literalRMatrix q3 w3) =
      (1_805_872_013 : ZMod q3) := by
  have h29pow : (29 : ZMod q3) ^ 14 ≠ 0 := by
    unfold q3
    reduce_mod_char
    decide +kernel
  apply mul_left_cancel₀ h29pow
  calc
    (29 : ZMod q3) ^ 14 * Matrix.permanent (literalRMatrix q3 w3) =
        Matrix.permanent ((29 : ZMod q3) • literalRMatrix q3 w3) := by
      rw [Matrix.permanent_smul, Fintype.card_fin]
    _ = Matrix.permanent residueMatrix3 := by
      rw [← residueMatrix3_eq_scaled_literalR]
    _ = permanentValue3 := hscaled
    _ = (29 : ZMod q3) ^ 14 * (1_805_872_013 : ZMod q3) := by
      unfold permanentValue3 q3
      reduce_mod_char

/-- The finite-field expression `-G_q * per(R_q)` from equation (3.1). -/
def finiteTPrimeResidue (q : ℕ) [Fact (Nat.Prime q)]
    (w : ZMod q) : ZMod q :=
  -literalGauss q w * Matrix.permanent (literalRMatrix q w)

theorem table1_tPrimeResidue_q1_of_scaled
    (hscaled : Matrix.permanent residueMatrix1 = permanentValue1) :
    finiteTPrimeResidue q1 w1 = (51_284_286 : ZMod q1) := by
  unfold finiteTPrimeResidue
  rw [literalGauss1_value, table1_permanent_q1_of_scaled hscaled]
  unfold q1
  reduce_mod_char

theorem table1_tPrimeResidue_q2_of_scaled
    (hscaled : Matrix.permanent residueMatrix2 = permanentValue2) :
    finiteTPrimeResidue q2 w2 = (95_468_454 : ZMod q2) := by
  unfold finiteTPrimeResidue
  rw [literalGauss2_value, table1_permanent_q2_of_scaled hscaled]
  unfold q2
  reduce_mod_char

theorem table1_tPrimeResidue_q3_of_scaled
    (hscaled : Matrix.permanent residueMatrix3 = permanentValue3) :
    finiteTPrimeResidue q3 w3 = (115_105_862 : ZMod q3) := by
  unfold finiteTPrimeResidue
  rw [literalGauss3_value, table1_permanent_q3_of_scaled hscaled]
  unfold q3
  reduce_mod_char

/-! A lightweight packed entry point.  A future unconditional checkpoint
theorem can be passed here without being imported by this file. -/

theorem table1_permanent_q1_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent (literalRMatrix q1 w1) =
      (1_767_907_462 : ZMod q1) :=
  table1_permanent_q1_of_scaled (permanent1_of_pack hpack)

theorem table1_permanent_q2_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent (literalRMatrix q2 w2) =
      (1_110_131_281 : ZMod q2) :=
  table1_permanent_q2_of_scaled (permanent2_of_pack hpack)

theorem table1_permanent_q3_of_pack
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Matrix.permanent (literalRMatrix q3 w3) =
      (1_805_872_013 : ZMod q3) :=
  table1_permanent_q3_of_scaled (permanent3_of_pack hpack)

/-! ## The direct three-modulus CRT congruence -/

/-- The integer `N` displayed in equation (3.2). -/
def sectionThreeN : ℤ := 84_643_985_981_440

/-- The product of the three Table 1 moduli. -/
def sectionThreeModulus : ℤ := (q1 : ℤ) * (q2 : ℤ) * (q3 : ℤ)

theorem sectionThreeModulus_value :
    sectionThreeModulus =
      7_999_971_276_033_184_729_821_198_209 := by
  norm_num [sectionThreeModulus, q1, q2, q3]

theorem sectionThreeN_mod_q1 :
    (sectionThreeN : ZMod q1) = (51_284_286 : ZMod q1) := by
  unfold sectionThreeN q1
  reduce_mod_char

theorem sectionThreeN_mod_q2 :
    (sectionThreeN : ZMod q2) = (95_468_454 : ZMod q2) := by
  unfold sectionThreeN q2
  reduce_mod_char

theorem sectionThreeN_mod_q3 :
    (sectionThreeN : ZMod q3) = (115_105_862 : ZMod q3) := by
  unfold sectionThreeN q3
  reduce_mod_char

private theorem modulus_dvd_sub_of_zmod_eq
    (q : ℕ) (a b : ℤ)
    (h : (a : ZMod q) = (b : ZMod q)) :
    (q : ℤ) ∣ a - b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa using sub_eq_zero.mpr h

/-- Direct CRT reconstruction of equation (3.2).

The quantity being reconstructed is an explicit `t : ℤ`; this is precisely
where an application to Sun's analytic `t'_29` must supply integrality and the
three finite-field specialization equalities. -/
theorem sectionThree_crt_congruence
    (t : ℤ)
    (h1 : (t : ZMod q1) = (51_284_286 : ZMod q1))
    (h2 : (t : ZMod q2) = (95_468_454 : ZMod q2))
    (h3 : (t : ZMod q3) = (115_105_862 : ZMod q3)) :
    t ≡ sectionThreeN [ZMOD sectionThreeModulus] := by
  have ht1 : (t : ZMod q1) = (sectionThreeN : ZMod q1) :=
    h1.trans sectionThreeN_mod_q1.symm
  have ht2 : (t : ZMod q2) = (sectionThreeN : ZMod q2) :=
    h2.trans sectionThreeN_mod_q2.symm
  have ht3 : (t : ZMod q3) = (sectionThreeN : ZMod q3) :=
    h3.trans sectionThreeN_mod_q3.symm
  have hd1 : (q1 : ℤ) ∣ t - sectionThreeN :=
    modulus_dvd_sub_of_zmod_eq q1 t sectionThreeN ht1
  have hd2 : (q2 : ℤ) ∣ t - sectionThreeN :=
    modulus_dvd_sub_of_zmod_eq q2 t sectionThreeN ht2
  have hd3 : (q3 : ℤ) ∣ t - sectionThreeN :=
    modulus_dvd_sub_of_zmod_eq q3 t sectionThreeN ht3
  have hd12 : ((q1 : ℤ) * (q2 : ℤ)) ∣ t - sectionThreeN := by
    exact (by decide +kernel : IsCoprime (q1 : ℤ) (q2 : ℤ)).mul_dvd hd1 hd2
  have hd123 : ((q1 : ℤ) * (q2 : ℤ) * (q3 : ℤ)) ∣
      t - sectionThreeN := by
    exact (by decide +kernel : IsCoprime
      ((q1 : ℤ) * (q2 : ℤ)) (q3 : ℤ)).mul_dvd hd12 hd3
  have hmodulus : sectionThreeModulus ∣ t - sectionThreeN := by
    simpa [sectionThreeModulus] using hd123
  have hreverse : sectionThreeN ≡ t [ZMOD sectionThreeModulus] :=
    (Int.modEq_iff_dvd).2 hmodulus
  exact hreverse.symm

end ScalarFiniteFieldCertificate
end SunCotangent
