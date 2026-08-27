import SunCotangent.AnalyticBridge
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Archimedean certificate for the `p = 29` cotangent permanent

This file formalizes the elementary size argument in Section 3 of the paper.
It contains no finite permanent computation.  The main ingredients are:

* reduction of every nonzero residue modulo `29` to one of `1, ..., 28`;
* monotonicity of tangent on `(0, pi / 2)` and the symmetries of cotangent;
* the triangle-inequality bound for a matrix permanent;
* the two exact integer inequalities used in the centered CRT argument; and
* a direct uniqueness theorem for an integer in the Archimedean interval.
-/

open scoped BigOperators

open Finset

namespace SunCotangent
namespace ArchimedeanCertificate

/-! ## Cotangent bounds -/

/-- Reflection in `pi / 2` changes the sign of the real cotangent. -/
private theorem cot_pi_sub (x : ℝ) :
    Real.cot (Real.pi - x) = -Real.cot x := by
  simp [Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- The real cotangent has period `pi`. -/
private theorem cot_add_nat_mul_pi (x : ℝ) (n : ℕ) :
    Real.cot (x + n * Real.pi) = Real.cot x := by
  simp only [Real.cot_eq_cos_div_sin, Real.cos_add_nat_mul_pi,
    Real.sin_add_nat_mul_pi]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))

/-- On the first half of the nonzero residue system, cotangent is positive
and decreases from its value at `pi / 29`. -/
private theorem abs_cot_le_first_of_one_le_of_le_fourteen
    (r : ℕ) (hr1 : 1 ≤ r) (hr14 : r ≤ 14) :
    |Real.cot (Real.pi * (r : ℝ) / 29)| ≤ Real.cot (Real.pi / 29) := by
  have hx0pos : 0 < Real.pi / 29 := by positivity
  have hx0lt : Real.pi / 29 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hxrpos : 0 < Real.pi * (r : ℝ) / 29 := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr1)
    positivity
  have hxrlt : Real.pi * (r : ℝ) / 29 < Real.pi / 2 := by
    calc
      Real.pi * (r : ℝ) / 29 ≤ Real.pi * 14 / 29 := by
        gcongr
        exact_mod_cast hr14
      _ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hx0le : Real.pi / 29 ≤ Real.pi * (r : ℝ) / 29 := by
    calc
      Real.pi / 29 = Real.pi * (1 : ℝ) / 29 := by ring
      _ ≤ Real.pi * (r : ℝ) / 29 := by
        gcongr
        exact_mod_cast hr1
  have htan0 : 0 < Real.tan (Real.pi / 29) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx0pos hx0lt
  have htanr : 0 < Real.tan (Real.pi * (r : ℝ) / 29) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hxrpos hxrlt
  have htanle :
      Real.tan (Real.pi / 29) ≤ Real.tan (Real.pi * (r : ℝ) / 29) := by
    rcases eq_or_lt_of_le hx0le with h | h
    · exact h ▸ le_rfl
    · exact (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0pos.le hxrlt h).le
  have hcotr : 0 ≤ Real.cot (Real.pi * (r : ℝ) / 29) := by
    rw [← Real.tan_inv_eq_cot]
    exact (inv_pos.mpr htanr).le
  rw [abs_of_nonneg hcotr]
  simpa only [Real.tan_inv_eq_cot] using
    ((inv_le_inv₀ htanr htan0).2 htanle)

/-- For every representative `r = 1, ..., 28`, the absolute value is
maximized at the two nearest nonzero residues `1` and `28`. -/
theorem abs_cot_pi_mul_div_twentyNine_le
    (r : ℕ) (hr1 : 1 ≤ r) (hr28 : r ≤ 28) :
    |Real.cot (Real.pi * (r : ℝ) / 29)| ≤ Real.cot (Real.pi / 29) := by
  by_cases hr14 : r ≤ 14
  · exact abs_cot_le_first_of_one_le_of_le_fourteen r hr1 hr14
  · let s := 29 - r
    have hs1 : 1 ≤ s := by
      dsimp [s]
      omega
    have hs14 : s ≤ 14 := by
      dsimp [s]
      omega
    have hcast : (s : ℝ) = 29 - (r : ℝ) := by
      dsimp [s]
      rw [Nat.cast_sub (by omega : r ≤ 29)]
      norm_num
    have hangle :
        Real.pi * (r : ℝ) / 29 = Real.pi - Real.pi * (s : ℝ) / 29 := by
      rw [hcast]
      ring
    calc
      |Real.cot (Real.pi * (r : ℝ) / 29)| =
          |Real.cot (Real.pi - Real.pi * (s : ℝ) / 29)| := by rw [hangle]
      _ = |-Real.cot (Real.pi * (s : ℝ) / 29)| := by rw [cot_pi_sub]
      _ = |Real.cot (Real.pi * (s : ℝ) / 29)| := abs_neg _
      _ ≤ Real.cot (Real.pi / 29) :=
        abs_cot_le_first_of_one_le_of_le_fourteen s hs1 hs14

/-- The strict estimate `cot (pi / 29) < 29 / pi`, obtained from
`x < tan x` on `(0, pi / 2)`. -/
theorem cot_pi_div_twentyNine_lt_twentyNine_div_pi :
    Real.cot (Real.pi / 29) < 29 / Real.pi := by
  have hxpos : 0 < Real.pi / 29 := by positivity
  have hxlt : Real.pi / 29 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have htanpos : 0 < Real.tan (Real.pi / 29) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hxpos hxlt
  have htan : Real.pi / 29 < Real.tan (Real.pi / 29) :=
    Real.lt_tan hxpos hxlt
  calc
    Real.cot (Real.pi / 29) = (Real.tan (Real.pi / 29))⁻¹ :=
      (Real.tan_inv_eq_cot (Real.pi / 29)).symm
    _ < (Real.pi / 29)⁻¹ := (inv_lt_inv₀ htanpos hxpos).2 htan
    _ = 29 / Real.pi := by field_simp [Real.pi_ne_zero]

/-- The elementary lower bound `3 < pi` supplies the rational endpoint. -/
theorem twentyNine_div_pi_lt_twentyNine_div_three :
    (29 : ℝ) / Real.pi < 29 / 3 := by
  apply (div_lt_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 3)).2
  nlinarith [Real.pi_gt_three]

/-- The full pointwise chain from Section 3, with the final strict rational
bound exposed for subsequent estimates. -/
theorem abs_cot_pi_mul_div_twentyNine_lt_twentyNine_div_three
    (r : ℕ) (hr1 : 1 ≤ r) (hr28 : r ≤ 28) :
    |Real.cot (Real.pi * (r : ℝ) / 29)| < 29 / 3 :=
  (abs_cot_pi_mul_div_twentyNine_le r hr1 hr28).trans_lt
    (cot_pi_div_twentyNine_lt_twentyNine_div_pi.trans
      twentyNine_div_pi_lt_twentyNine_div_three)

/-- Reduction modulo `29` extends the representative bound to every
positive exponent not divisible by `29`. -/
theorem abs_cot_pi_mul_nat_div_twentyNine_lt_twentyNine_div_three
    (e : ℕ) (he : ¬29 ∣ e) :
    |Real.cot (Real.pi * (e : ℝ) / 29)| < 29 / 3 := by
  let r := e % 29
  have hr0 : r ≠ 0 := by
    dsimp [r]
    simpa only [Nat.dvd_iff_mod_eq_zero] using he
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  have hr28 : r ≤ 28 := by
    have hrlt : r < 29 := by
      dsimp [r]
      exact Nat.mod_lt _ (by norm_num)
    omega
  have hdecomp : e % 29 + 29 * (e / 29) = e := Nat.mod_add_div e 29
  have hdecompReal :
      ((e % 29 : ℕ) : ℝ) + 29 * ((e / 29 : ℕ) : ℝ) = (e : ℝ) := by
    exact_mod_cast hdecomp
  have hangle :
      Real.pi * (e : ℝ) / 29 =
        Real.pi * (r : ℝ) / 29 + (e / 29 : ℕ) * Real.pi := by
    dsimp [r]
    rw [← hdecompReal]
    ring
  calc
    |Real.cot (Real.pi * (e : ℝ) / 29)| =
        |Real.cot (Real.pi * (r : ℝ) / 29 + (e / 29 : ℕ) * Real.pi)| := by
      rw [hangle]
    _ = |Real.cot (Real.pi * (r : ℝ) / 29)| := by
      rw [cot_add_nat_mul_pi]
    _ < 29 / 3 :=
      abs_cot_pi_mul_div_twentyNine_lt_twentyNine_div_three r hr1 hr28

/-- Every entry of the actual `14 x 14` cotangent matrix satisfies the
strict rational bound from the paper. -/
theorem realCotMatrix29_entry_abs_lt (j k : Half29) :
    |realCotMatrix29 j k| < 29 / 3 := by
  simpa only [realCotMatrix29, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    abs_cot_pi_mul_nat_div_twentyNine_lt_twentyNine_div_three
      ((j.val + 1) * (k.val + 1)) (indexProduct29_not_dvd j k)

/-! ## Permanent and square-root bounds -/

/-- A generic triangle-inequality estimate for a real matrix permanent. -/
theorem abs_permanent_le_factorial_mul_pow
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : ℝ)
    (hA : ∀ i j, |A i j| ≤ C) :
    |A.permanent| ≤ (n.factorial : ℝ) * C ^ n := by
  classical
  rw [Matrix.permanent]
  calc
    |∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, A (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin n), |∏ i : Fin n, A (σ i) i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      exact Finset.abs_prod _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ _i : Fin n, C := by
      apply Finset.sum_le_sum
      intro σ _hσ
      exact Finset.prod_le_prod
        (fun i _hi ↦ abs_nonneg (A (σ i) i))
        (fun i _hi ↦ hA (σ i) i)
    _ = (n.factorial : ℝ) * C ^ n := by
      simp [Fintype.card_perm]

/-- The permanent itself is bounded by `14! (29 / 3)^14`. -/
theorem abs_realCotMatrix29_permanent_le :
    |realCotMatrix29.permanent| ≤
      (Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14 := by
  apply abs_permanent_le_factorial_mul_pow
  intro i j
  exact (realCotMatrix29_entry_abs_lt i j).le

/-- The square-root factor is strictly smaller than `6`. -/
theorem sqrt_twentyNine_lt_six : Real.sqrt 29 < 6 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 29),
    Real.sqrt_nonneg (29 : ℝ)]

/-- The Archimedean estimate for the integer represented by the cotangent
permanent.  This is equation (3.4) in the paper. -/
theorem abs_sqrt_twentyNine_mul_realCotMatrix29_permanent_lt :
    |Real.sqrt 29 * realCotMatrix29.permanent| <
      6 * (Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14 := by
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (29 : ℝ))]
  calc
    Real.sqrt 29 * |realCotMatrix29.permanent| ≤
        Real.sqrt 29 *
          ((Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14) :=
      mul_le_mul_of_nonneg_left abs_realCotMatrix29_permanent_le
        (Real.sqrt_nonneg (29 : ℝ))
    _ < 6 * ((Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14) := by
      apply mul_lt_mul_of_pos_right sqrt_twentyNine_lt_six
      positivity
    _ = 6 * (Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14 := by ring

/-! ## Exact CRT separation inequalities -/

/-- The three-prime CRT modulus displayed in Section 3 of the paper. -/
def paperCRTModulus : ℤ :=
  7_999_971_276_033_184_729_821_198_209

/-- The centered CRT representative displayed in Section 3 of the paper. -/
def paperClaimedValue : ℤ :=
  84_643_985_981_440

/-- The first exact decimal expansion displayed below equation (3.4). -/
theorem paperCRTModulus_mul_three_pow_fourteen :
    paperCRTModulus * 3 ^ 14 =
      38_263_614_614_157_165_534_008_166_576_502_521 := by
  norm_num [paperCRTModulus]

/-- The second exact decimal expansion displayed below equation (3.4). -/
theorem twice_archimedean_numerator_value :
    12 * (Nat.factorial 14 : ℤ) * 29 ^ 14 =
      311_287_419_086_018_409_841_804_604_006_400 := by
  norm_num [Nat.factorial]

/-- The exact scaled value of the centered CRT representative. -/
theorem paperClaimedValue_mul_three_pow_fourteen :
    paperClaimedValue * 3 ^ 14 =
      404_849_560_985_662_095_360 := by
  norm_num [paperClaimedValue]

/-- The exact numerator of the Archimedean interval. -/
theorem archimedean_numerator_value :
    6 * (Nat.factorial 14 : ℤ) * 29 ^ 14 =
      155_643_709_543_009_204_920_902_302_003_200 := by
  norm_num [Nat.factorial]

/-- Twice the rational Archimedean numerator is smaller than the scaled
CRT modulus. -/
theorem twice_archimedean_numerator_lt_scaled_modulus :
    paperCRTModulus * 3 ^ 14 >
      12 * (Nat.factorial 14 : ℤ) * 29 ^ 14 := by
  norm_num [paperCRTModulus, Nat.factorial]

/-- The claimed representative lies strictly inside the Archimedean
interval after clearing the denominator `3^14`. -/
theorem claimedValue_scaled_lt_archimedean_numerator :
    paperClaimedValue * 3 ^ 14 <
      6 * (Nat.factorial 14 : ℤ) * 29 ^ 14 := by
  norm_num [paperClaimedValue, Nat.factorial]

/-! ## Uniqueness in the Archimedean interval -/

/-- Generic uniqueness principle: two congruent integers whose absolute
values have sum smaller than the modulus are equal. -/
theorem eq_of_modEq_of_abs_add_abs_lt
    {z n m : ℤ} (hcong : z ≡ n [ZMOD m])
    (hsmall : |z| + |n| < m) : z = n := by
  have hdvd : m ∣ z - n := hcong.symm.dvd
  have hdabs : |z - n| < m := (abs_sub z n).trans_lt hsmall
  have hzero : z - n = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    simpa only [Int.natAbs_abs] using
      Int.natAbs_lt_natAbs_of_nonneg_of_lt (abs_nonneg (z - n)) hdabs
  exact sub_eq_zero.mp hzero

/-- Direct integer-scaled form of the paper's uniqueness argument. -/
theorem eq_paperClaimedValue_of_modEq_of_scaled_abs_lt
    (z : ℤ) (hcong : z ≡ paperClaimedValue [ZMOD paperCRTModulus])
    (hz : |z| * 3 ^ 14 <
      6 * (Nat.factorial 14 : ℤ) * 29 ^ 14) :
    z = paperClaimedValue := by
  apply eq_of_modEq_of_abs_add_abs_lt hcong
  have hclaimedNonneg : 0 ≤ paperClaimedValue := by
    norm_num [paperClaimedValue]
  have hscaled :
      (|z| + |paperClaimedValue|) * 3 ^ 14 <
        paperCRTModulus * 3 ^ 14 := by
    calc
      (|z| + |paperClaimedValue|) * 3 ^ 14 =
          |z| * 3 ^ 14 + paperClaimedValue * 3 ^ 14 := by
        rw [abs_of_nonneg hclaimedNonneg]
        ring
      _ < 6 * (Nat.factorial 14 : ℤ) * 29 ^ 14 +
          6 * (Nat.factorial 14 : ℤ) * 29 ^ 14 :=
        add_lt_add hz claimedValue_scaled_lt_archimedean_numerator
      _ = 12 * (Nat.factorial 14 : ℤ) * 29 ^ 14 := by ring
      _ < paperCRTModulus * 3 ^ 14 :=
        twice_archimedean_numerator_lt_scaled_modulus
  exact lt_of_mul_lt_mul_right hscaled (by positivity)

/-- Real-valued form of the uniqueness theorem, using exactly the
Archimedean interval stated in the paper. -/
theorem eq_paperClaimedValue_of_modEq_of_archimedean_bound
    (z : ℤ) (hcong : z ≡ paperClaimedValue [ZMOD paperCRTModulus])
    (hz : (|z| : ℝ) <
      6 * (Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14) :
    z = paperClaimedValue := by
  apply eq_paperClaimedValue_of_modEq_of_scaled_abs_lt z hcong
  have hzScaledReal :
      (|z| : ℝ) * (3 : ℝ) ^ 14 <
        6 * (Nat.factorial 14 : ℝ) * (29 : ℝ) ^ 14 := by
    calc
      (|z| : ℝ) * (3 : ℝ) ^ 14 <
          (6 * (Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14) *
            (3 : ℝ) ^ 14 := mul_lt_mul_of_pos_right hz (by positivity)
      _ = 6 * (Nat.factorial 14 : ℝ) * (29 : ℝ) ^ 14 := by ring
  exact_mod_cast hzScaledReal

/-- Final direct bridge: an integral value represented by the analytic
cotangent permanent and congruent to the CRT representative must be the
claimed integer. -/
theorem eq_paperClaimedValue_of_modEq_of_cotangent_identity
    (z : ℤ) (hcong : z ≡ paperClaimedValue [ZMOD paperCRTModulus])
    (hreal : (z : ℝ) = Real.sqrt 29 * realCotMatrix29.permanent) :
    z = paperClaimedValue := by
  apply eq_paperClaimedValue_of_modEq_of_archimedean_bound z hcong
  rw [hreal]
  exact abs_sqrt_twentyNine_mul_realCotMatrix29_permanent_lt

end ArchimedeanCertificate
end SunCotangent
