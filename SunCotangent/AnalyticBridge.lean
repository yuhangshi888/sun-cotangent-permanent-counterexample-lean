import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The analytic bridge for the `p = 29` cotangent permanent

This file contains no computational certificate.  It proves the analytic facts needed to turn
the cyclotomic certificate into the advertised identity for the ordinary real cotangent
permanent:

* `zeta29` is the standard primitive twenty-ninth root `exp (2 * pi * I / 29)`;
* the square-sum Gauss value at `zeta29` is the **positive** square root of `29`;
* `cot (pi * e / 29) = I * (zeta29^e + 1) / (zeta29^e - 1)`;
* multiplying every entry of a `14 x 14` matrix by a scalar multiplies its permanent by the
  fourteenth power of that scalar;
* an exact cyclotomic certificate for the scaled root-of-unity matrix therefore implies the
  claimed real cotangent-permanent value.

The sign of the Gauss sum is not assumed.  Its square is obtained from Mathlib's quadratic
Gauss-sum theorem, while positivity follows from an explicit seven-cosine expression.  The
negative cosine terms are paired with larger positive cosine terms, using strict monotonicity of
cosine on `[0, pi]`.
-/

open scoped BigOperators ComplexConjugate

open Finset

namespace SunCotangent

local instance primeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- The matrix size `(29 - 1) / 2`. -/
abbrev Half29 := Fin 14

/-- The standard primitive twenty-ninth root of unity. -/
noncomputable def zeta29 : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((29 : ℕ) : ℂ))

theorem zeta29_isPrimitiveRoot : IsPrimitiveRoot zeta29 29 := by
  simpa only [zeta29] using Complex.isPrimitiveRoot_exp 29 (by norm_num)

@[simp]
theorem zeta29_pow_twentyNine : zeta29 ^ 29 = 1 :=
  zeta29_isPrimitiveRoot.pow_eq_one

theorem zeta29_pow_eq_pow_mod (n : ℕ) : zeta29 ^ n = zeta29 ^ (n % 29) :=
  pow_eq_pow_mod n zeta29_pow_twentyNine

theorem zeta29_pow_ne_one {n : ℕ} (hn : ¬29 ∣ n) : zeta29 ^ n ≠ 1 := by
  exact fun h ↦ hn ((zeta29_isPrimitiveRoot.pow_eq_one_iff_dvd n).mp h)

/-- The additive character of `ZMod 29` associated with `zeta29`. -/
noncomputable def psi29 : AddChar (ZMod 29) ℂ :=
  AddChar.zmodChar 29 zeta29_pow_twentyNine

theorem psi29_isPrimitive : AddChar.IsPrimitive psi29 := by
  exact AddChar.zmodChar_primitive_of_primitive_root 29 zeta29_isPrimitiveRoot

theorem psi29_ne_one : psi29 ≠ 1 := by
  intro h
  exact (psi29_isPrimitive (a := (1 : ZMod 29)) one_ne_zero) (by simp [h])

/-- The quadratic character of `ZMod 29`, with its integer values embedded in `ℂ`. -/
noncomputable def chi29 : MulChar (ZMod 29) ℂ :=
  (quadraticChar (ZMod 29)).ringHomComp (Int.castRingHom ℂ)

theorem chi29_ne_one : chi29 ≠ 1 := by
  rw [chi29, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
  exact quadraticChar_ne_one (by norm_num [ZMod.ringChar_zmod_n])

theorem chi29_isQuadratic : MulChar.IsQuadratic chi29 := by
  exact (quadraticChar_isQuadratic (ZMod 29)).comp (Int.castRingHom ℂ)

/-- The square-sum form of the quadratic Gauss sum.  This is also the evaluation at `zeta29` of
`sum_(a=0)^28 X^(a^2)`, the polynomial used in the cyclotomic certificate. -/
noncomputable def gauss29 : ℂ :=
  ∑ a : Fin 29, zeta29 ^ (a.val ^ 2)

/-- Fiber-counting identity converting a square-sum into the usual character Gauss sum. -/
theorem sum_addChar_sq_eq_gaussSum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (psi : AddChar F ℂ) (hpsi : psi ≠ 1) :
    (∑ x : F, psi (x ^ 2)) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) psi := by
  classical
  rw [← Fintype.sum_fiberwise' (fun x : F ↦ x ^ 2) (fun y : F ↦ psi y)]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard (y : F) :
      (Fintype.card {x : F // x ^ 2 = y} : ℤ) = quadraticChar F y + 1 := by
    let e : {x : F // x ^ 2 = y} ≃ ↑({x : F | x ^ 2 = y} : Set F) := {
      toFun x := ⟨x.1, x.2⟩
      invFun x := ⟨x.1, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [Fintype.card_congr e, ← Set.toFinset_card]
    exact quadraticChar_card_sqrts hF y
  simp_rw [show ∀ y : F,
      (Fintype.card {x : F // x ^ 2 = y} : ℂ) =
        (quadraticChar F y : ℂ) + 1 by
      intro y
      exact_mod_cast hcard y]
  rw [gaussSum]
  simp only [MulChar.ringHomComp_apply, add_mul, one_mul,
    Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hpsi, add_zero]
  rfl

theorem gauss29_eq_gaussSum : gauss29 = gaussSum chi29 psi29 := by
  classical
  calc
    gauss29 = ∑ x : ZMod 29, psi29 (x ^ 2) := by
      rw [gauss29]
      refine Fintype.sum_equiv (ZMod.finEquiv 29) _ _ ?_
      intro a
      rw [psi29, AddChar.zmodChar_apply]
      have hval : ((ZMod.finEquiv 29 a) ^ 2).val = (a.val ^ 2) % 29 := by
        have hfin : (ZMod.finEquiv 29 a).val = a.val := rfl
        rw [pow_two, ZMod.val_mul, hfin, pow_two]
      calc
        zeta29 ^ (a.val ^ 2) = zeta29 ^ ((a.val ^ 2) % 29) :=
          zeta29_pow_eq_pow_mod _
        _ = zeta29 ^ ((ZMod.finEquiv 29 a) ^ 2).val := by rw [hval]
    _ = gaussSum chi29 psi29 := by
      simpa only [chi29] using
        sum_addChar_sq_eq_gaussSum (F := ZMod 29)
          (by norm_num [ZMod.ringChar_zmod_n]) psi29 psi29_ne_one

theorem gauss29_sq : gauss29 ^ 2 = (29 : ℂ) := by
  rw [gauss29_eq_gaussSum]
  have h := gaussSum_sq chi29_ne_one chi29_isQuadratic
    (ψ := psi29) psi29_isPrimitive
  have hchi : chi29 (-1) = 1 := by
    rw [chi29, MulChar.ringHomComp_apply,
      quadraticChar_neg_one (by norm_num [ZMod.ringChar_zmod_n]),
      ZMod.card, ZMod.χ₄_nat_eq_if_mod_four]
    norm_num
  rw [hchi] at h
  simpa only [one_mul, ZMod.card, Nat.cast_ofNat] using h

/-- Powers of `zeta29` written in the form expected by Euler's formula. -/
theorem zeta29_pow_eq_exp_mul_I (n : ℕ) :
    zeta29 ^ n =
      Complex.exp (((2 * Real.pi * n / 29 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta29, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Pairing conjugate powers of `zeta29` gives a real cosine. -/
theorem zeta29_pow_add_complement (n : ℕ) (hn : n ≤ 29) :
    zeta29 ^ n + zeta29 ^ (29 - n) =
      (2 * Real.cos (2 * Real.pi * n / 29) : ℝ) := by
  rw [zeta29_pow_eq_exp_mul_I, zeta29_pow_eq_exp_mul_I]
  have hangle : 2 * Real.pi * (29 - n : ℕ) / 29 =
      2 * Real.pi - 2 * Real.pi * n / 29 := by
    push_cast [hn]
    ring
  rw [hangle, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_two_pi_sub,
    Real.sin_two_pi_sub]
  push_cast
  ring

/-- The explicit quadratic-residue expansion of the square-sum. -/
theorem gauss29_eq_residue_sum :
    gauss29 = 1 + 2 *
      (zeta29 ^ 1 + zeta29 ^ 28 + zeta29 ^ 4 + zeta29 ^ 25 +
       zeta29 ^ 5 + zeta29 ^ 24 + zeta29 ^ 6 + zeta29 ^ 23 +
       zeta29 ^ 7 + zeta29 ^ 22 + zeta29 ^ 9 + zeta29 ^ 20 +
       zeta29 ^ 13 + zeta29 ^ 16) := by
  rw [gauss29]
  calc
    (∑ a : Fin 29, zeta29 ^ (a.val ^ 2)) =
        ∑ a : Fin 29, zeta29 ^ ((a.val ^ 2) % 29) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact zeta29_pow_eq_pow_mod _
    _ = 1 + 2 *
        (zeta29 ^ 1 + zeta29 ^ 28 + zeta29 ^ 4 + zeta29 ^ 25 +
         zeta29 ^ 5 + zeta29 ^ 24 + zeta29 ^ 6 + zeta29 ^ 23 +
         zeta29 ^ 7 + zeta29 ^ 22 + zeta29 ^ 9 + zeta29 ^ 20 +
         zeta29 ^ 13 + zeta29 ^ 16) := by
      simp only [Fin.sum_univ_succ]
      norm_num
      ring

/-- A real seven-cosine expression for the quadratic Gauss sum. -/
theorem gauss29_eq_cosine_sum :
    gauss29 =
      (1 + 4 *
        (Real.cos (2 * Real.pi / 29) + Real.cos (8 * Real.pi / 29) +
         Real.cos (10 * Real.pi / 29) + Real.cos (12 * Real.pi / 29) +
         Real.cos (14 * Real.pi / 29) + Real.cos (18 * Real.pi / 29) +
         Real.cos (26 * Real.pi / 29)) : ℝ) := by
  rw [gauss29_eq_residue_sum]
  have h1 := zeta29_pow_add_complement 1 (by norm_num)
  have h4 := zeta29_pow_add_complement 4 (by norm_num)
  have h5 := zeta29_pow_add_complement 5 (by norm_num)
  have h6 := zeta29_pow_add_complement 6 (by norm_num)
  have h7 := zeta29_pow_add_complement 7 (by norm_num)
  have h9 := zeta29_pow_add_complement 9 (by norm_num)
  have h13 := zeta29_pow_add_complement 13 (by norm_num)
  norm_num only at h1 h4 h5 h6 h7 h9 h13
  have h1angle : 2 * Real.pi * (1 : ℝ) / 29 = 2 * Real.pi / 29 := by ring
  have h4angle : 2 * Real.pi * (4 : ℝ) / 29 = 8 * Real.pi / 29 := by ring
  have h5angle : 2 * Real.pi * (5 : ℝ) / 29 = 10 * Real.pi / 29 := by ring
  have h6angle : 2 * Real.pi * (6 : ℝ) / 29 = 12 * Real.pi / 29 := by ring
  have h7angle : 2 * Real.pi * (7 : ℝ) / 29 = 14 * Real.pi / 29 := by ring
  have h9angle : 2 * Real.pi * (9 : ℝ) / 29 = 18 * Real.pi / 29 := by ring
  have h13angle : 2 * Real.pi * (13 : ℝ) / 29 = 26 * Real.pi / 29 := by ring
  rw [h1angle] at h1
  rw [h4angle] at h4
  rw [h5angle] at h5
  rw [h6angle] at h6
  rw [h7angle] at h7
  rw [h9angle] at h9
  rw [h13angle] at h13
  simp only [pow_one] at h1
  simp only [pow_one]
  calc
    (1 : ℂ) + (2 : ℂ) *
        (zeta29 + zeta29 ^ 28 + zeta29 ^ 4 + zeta29 ^ 25 +
         zeta29 ^ 5 + zeta29 ^ 24 + zeta29 ^ 6 + zeta29 ^ 23 +
         zeta29 ^ 7 + zeta29 ^ 22 + zeta29 ^ 9 + zeta29 ^ 20 +
         zeta29 ^ 13 + zeta29 ^ 16) =
        (1 : ℂ) + (2 : ℂ) *
          ((zeta29 + zeta29 ^ 28) + (zeta29 ^ 4 + zeta29 ^ 25) +
           (zeta29 ^ 5 + zeta29 ^ 24) + (zeta29 ^ 6 + zeta29 ^ 23) +
           (zeta29 ^ 7 + zeta29 ^ 22) + (zeta29 ^ 9 + zeta29 ^ 20) +
           (zeta29 ^ 13 + zeta29 ^ 16)) := by ring
    _ = ((1 + 4 *
        (Real.cos (2 * Real.pi / 29) + Real.cos (8 * Real.pi / 29) +
         Real.cos (10 * Real.pi / 29) + Real.cos (12 * Real.pi / 29) +
         Real.cos (14 * Real.pi / 29) + Real.cos (18 * Real.pi / 29) +
         Real.cos (26 * Real.pi / 29)) : ℝ) : ℂ) := by
      rw [h1, h4, h5, h6, h7, h9, h13]
      push_cast
      ring

/-- Positivity fixes the sign in the quadratic Gauss-sum evaluation. -/
theorem gauss29_re_pos : 0 < gauss29.re := by
  have h13angle : 26 * Real.pi / 29 = Real.pi - 3 * Real.pi / 29 := by ring
  have h9angle : 18 * Real.pi / 29 = Real.pi - 11 * Real.pi / 29 := by ring
  have h13pair :
      0 < Real.cos (2 * Real.pi / 29) + Real.cos (26 * Real.pi / 29) := by
    rw [h13angle, Real.cos_pi_sub]
    have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 2 * Real.pi / 29) (y := 3 * Real.pi / 29)
      (by positivity) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    linarith
  have h9pair :
      0 < Real.cos (8 * Real.pi / 29) + Real.cos (18 * Real.pi / 29) := by
    rw [h9angle, Real.cos_pi_sub]
    have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 8 * Real.pi / 29) (y := 11 * Real.pi / 29)
      (by positivity) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    linarith
  have h5 : 0 < Real.cos (10 * Real.pi / 29) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have h6 : 0 < Real.cos (12 * Real.pi / 29) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have h7 : 0 < Real.cos (14 * Real.pi / 29) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  rw [gauss29_eq_cosine_sum]
  change 0 < 1 + 4 *
    (Real.cos (2 * Real.pi / 29) + Real.cos (8 * Real.pi / 29) +
     Real.cos (10 * Real.pi / 29) + Real.cos (12 * Real.pi / 29) +
     Real.cos (14 * Real.pi / 29) + Real.cos (18 * Real.pi / 29) +
     Real.cos (26 * Real.pi / 29))
  nlinarith

/-- The quadratic Gauss sum for the chosen (positive-angle) primitive root has positive sign. -/
theorem gauss29_eq_sqrt : gauss29 = (Real.sqrt 29 : ℝ) := by
  have hsqrt_sq : ((Real.sqrt 29 : ℝ) : ℂ) ^ 2 = 29 := by
    norm_cast
    norm_num [Real.sq_sqrt]
  have hfactor :
      (gauss29 - (Real.sqrt 29 : ℝ)) * (gauss29 + (Real.sqrt 29 : ℝ)) = 0 := by
    calc
      (gauss29 - (Real.sqrt 29 : ℝ)) * (gauss29 + (Real.sqrt 29 : ℝ)) =
          gauss29 ^ 2 - ((Real.sqrt 29 : ℝ) : ℂ) ^ 2 := by ring
      _ = 0 := by rw [gauss29_sq, hsqrt_sq]; ring
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hneg : gauss29 = -((Real.sqrt 29 : ℝ) : ℂ) :=
      eq_neg_of_add_eq_zero_left h
    have hsqrt_nonneg : 0 ≤ Real.sqrt 29 := Real.sqrt_nonneg _
    have hpos := gauss29_re_pos
    rw [hneg] at hpos
    norm_num at hpos
    linarith

/-- The root-of-unity quotient appearing in the cyclotomic matrix. -/
noncomputable def rootRatio (u : ℂ) : ℂ :=
  (u + 1) / (u - 1)

/-- The standard exponential identity for cotangent.  This is valid even at a pole because
Lean's division is totalized; the zero-denominator case is handled explicitly below.  The
exponents used by `rootMatrix29` are subsequently proved not to be pole cases. -/
theorem cot_pi_mul_div_twentyNine (e : ℕ) :
    ((Real.cot (Real.pi * e / 29) : ℝ) : ℂ) =
      Complex.I * rootRatio (zeta29 ^ e) := by
  rw [Complex.ofReal_cot]
  have harg :
      ((Real.pi * e / 29 : ℝ) : ℂ) = Real.pi * ((e : ℂ) / 29) := by
    push_cast
    ring
  rw [harg, Complex.cot_pi_eq_exp_ratio]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ((e : ℂ) / 29)) = zeta29 ^ e := by
    rw [zeta29, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  simp only [rootRatio]
  by_cases h : zeta29 ^ e - 1 = 0
  · have heq : zeta29 ^ e = 1 := sub_eq_zero.mp h
    simp [heq]
  · have h' : 1 - zeta29 ^ e ≠ 0 :=
      sub_ne_zero.mpr (sub_ne_zero.mp h).symm
    field_simp [h, h', Complex.I_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The real cotangent matrix in the statement of the counterexample. -/
noncomputable def realCotMatrix29 : Matrix Half29 Half29 ℝ :=
  fun j k ↦ Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29)

/-- The same cotangent matrix, embedded entrywise in `ℂ`. -/
noncomputable def cotMatrix29 : Matrix Half29 Half29 ℂ :=
  fun j k ↦ (realCotMatrix29 j k : ℂ)

/-- The unscaled root-of-unity quotient matrix. -/
noncomputable def rootMatrix29 : Matrix Half29 Half29 ℂ :=
  fun j k ↦ rootRatio (zeta29 ^ ((j.val + 1) * (k.val + 1)))

/-- Every exponent occurring in the `14 × 14` matrix is nonzero modulo `29`. -/
theorem indexProduct29_not_dvd (j k : Half29) :
    ¬(29 : ℕ) ∣ (j.val + 1) * (k.val + 1) := by
  exact (show Nat.Prime 29 by decide).not_dvd_mul
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))

/-- Thus the denominator in every actual root-ratio matrix entry is genuinely nonzero. -/
theorem rootMatrix29_denominator_ne_zero (j k : Half29) :
    zeta29 ^ ((j.val + 1) * (k.val + 1)) - 1 ≠ 0 := by
  exact sub_ne_zero.mpr (zeta29_pow_ne_one (indexProduct29_not_dvd j k))

/-- The integral cyclotomic matrix specializes to `29` times `rootMatrix29`. -/
noncomputable def scaledRootMatrix29 : Matrix Half29 Half29 ℂ :=
  (29 : ℂ) • rootMatrix29

theorem cotMatrix29_eq_I_smul : cotMatrix29 = Complex.I • rootMatrix29 := by
  ext j k
  simp only [cotMatrix29, realCotMatrix29, rootMatrix29,
    Matrix.smul_apply, smul_eq_mul]
  convert cot_pi_mul_div_twentyNine ((j.val + 1) * (k.val + 1)) using 1
  push_cast
  ring

/-- Mapping a square matrix by a ring homomorphism commutes with the permanent. -/
theorem permanent_map
    {n R S : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (M : Matrix n n R) :
    (M.map f).permanent = f M.permanent := by
  simp only [Matrix.permanent, Matrix.map_apply, map_sum, map_prod]

theorem cotMatrix29_eq_map_real :
    cotMatrix29 = realCotMatrix29.map (Complex.ofRealHom) := by
  rfl

theorem ofReal_permanent_realCotMatrix29 :
    ((realCotMatrix29.permanent : ℝ) : ℂ) = cotMatrix29.permanent := by
  rw [cotMatrix29_eq_map_real, permanent_map]
  rfl

/-- Since `I^14 = -1`, the cotangent permanent is the negative root-ratio permanent. -/
theorem permanent_cotMatrix29 :
    cotMatrix29.permanent = -rootMatrix29.permanent := by
  rw [cotMatrix29_eq_I_smul, Matrix.permanent_smul]
  have hI : Complex.I ^ 14 = (-1 : ℂ) := by
    rw [show 14 = 2 * 7 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  rw [show Fintype.card Half29 = 14 by rfl]
  rw [hI]
  ring

/-- Scaling every entry of a fourteen-row square matrix contributes the fourteenth power. -/
theorem permanent_scaledRootMatrix29 :
    scaledRootMatrix29.permanent = (29 : ℂ) ^ 14 * rootMatrix29.permanent := by
  simp only [scaledRootMatrix29, Matrix.permanent_smul, Fintype.card_fin]

/-- Exact endgame: a cyclotomic certificate for `G * per(29 R)` implies the complex form of the
claimed cotangent-permanent identity. -/
theorem complex_cotangentPermanent29_value_of_certificate
    (hcertificate :
      gauss29 * scaledRootMatrix29.permanent =
        -(84643985981440 : ℂ) * (29 : ℂ) ^ 14) :
    (Real.sqrt 29 : ℝ) * cotMatrix29.permanent = (84643985981440 : ℂ) := by
  rw [gauss29_eq_sqrt, permanent_scaledRootMatrix29] at hcertificate
  rw [permanent_cotMatrix29]
  have hpow : (29 : ℂ) ^ 14 ≠ 0 := by norm_num
  apply (mul_left_cancel₀ hpow)
  calc
    (29 : ℂ) ^ 14 * ((Real.sqrt 29 : ℝ) * -rootMatrix29.permanent) =
        -(((Real.sqrt 29 : ℝ) : ℂ) *
          ((29 : ℂ) ^ 14 * rootMatrix29.permanent)) := by ring
    _ = -(-(84643985981440 : ℂ) * (29 : ℂ) ^ 14) := by rw [hcertificate]
    _ = (29 : ℂ) ^ 14 * (84643985981440 : ℂ) := by ring

/-- The real statement used by the advertised theorem. -/
theorem real_cotangentPermanent29_value_of_certificate
    (hcertificate :
      gauss29 * scaledRootMatrix29.permanent =
        -(84643985981440 : ℂ) * (29 : ℂ) ^ 14) :
    Real.sqrt 29 * realCotMatrix29.permanent = 84643985981440 := by
  apply Complex.ofReal_injective
  push_cast
  rw [ofReal_permanent_realCotMatrix29]
  exact complex_cotangentPermanent29_value_of_certificate hcertificate

end SunCotangent
