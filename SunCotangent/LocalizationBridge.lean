import SunCotangent.AnalyticBridge
import SunCotangent.LiteralSectionFourBounds
import SunCotangent.ScalarFiniteFieldCertificate

/-!
# The inverse identity and its finite-field specialization

The paper writes the inverse of `ζ^e - 1` as a polynomial in `ζ^e`.
No localization construction is needed to justify that formula: evaluate the
integral polynomial identity from Section 2 in a field, prove that the
denominator is nonzero, and use the ordinary field inverse.

The second half of this file performs the same argument for an arbitrary
prime field `ZMod q`.  Its hypotheses expose every condition used by the
specialization: `q` is prime, `w` has order exactly `29`, the exponent is
nonzero, and the image of `29` is nonzero.  No numerical entry table and no
final certificate value occurs here.
-/

open scoped BigOperators

namespace SunCotangent
namespace LocalizationBridge

open Polynomial
open CyclotomicCertificate
open LiteralSectionFourBounds
open ScalarFiniteFieldCertificate

noncomputable section

local instance primeFact29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-! ## Scalar evaluation of the paper's weighted polynomial -/

/-- Evaluation of the integral polynomial
`U(X) = ∑_(s=0)^27 (28-s)X^s` in an arbitrary commutative ring.  Defining
this through `sectionTwoUPolynomial` keeps the inverse formula tied directly
to the literal polynomial proved in Section 2. -/
def weightedUEval {R : Type*} [CommRing R] (t : R) : R :=
  Polynomial.eval₂ (Int.castRingHom R) t sectionTwoUPolynomial

/-- Expanded form of `weightedUEval`, matching `sectionFourU` and the
displayed sum in the paper term for term. -/
theorem weightedUEval_eq_sum
    {R : Type*} [CommRing R] (t : R) :
    weightedUEval t =
      ∑ s : Fin 28,
        ((28 - (s.val : ℤ) : ℤ) : R) * t ^ s.val := by
  simp [weightedUEval, sectionTwoUPolynomial,
    Polynomial.eval₂_finsetSum]

/-- A nontrivial twenty-ninth root kills `Φ₂₉`.  This proof uses the
factorization `Φ₂₉(X)(X-1)=X²⁹-1`; it does not construct a localization. -/
private theorem eval₂_cyclotomic_twentyNine_eq_zero
    {K : Type*} [Field K] (t : K)
    (ht : t ^ 29 = 1) (ht_ne_one : t ≠ 1) :
    Polynomial.eval₂ (Int.castRingHom K) t
      (Polynomial.cyclotomic 29 ℤ) = 0 := by
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht_ne_one
  have hproduct :
      Polynomial.eval₂ (Int.castRingHom K) t
          (Polynomial.cyclotomic 29 ℤ) * (t - 1) = 0 := by
    calc
      Polynomial.eval₂ (Int.castRingHom K) t
          (Polynomial.cyclotomic 29 ℤ) * (t - 1) =
          Polynomial.eval₂ (Int.castRingHom K) t
            (Polynomial.cyclotomic 29 ℤ * (X - 1)) := by
        simp
      _ = Polynomial.eval₂ (Int.castRingHom K) t (X ^ 29 - 1) := by
        rw [Polynomial.cyclotomic_prime_mul_X_sub_one ℤ 29]
      _ = 0 := by simp [ht]
  exact (mul_eq_zero.mp hproduct).resolve_right hden

/-- The evaluated telescoping identity
`(t-1)U(t)=-29` at every nontrivial twenty-ninth root. -/
theorem sub_one_mul_weightedUEval
    {K : Type*} [Field K] (t : K)
    (ht : t ^ 29 = 1) (ht_ne_one : t ≠ 1) :
    (t - 1) * weightedUEval t = -(29 : K) := by
  have hcyclotomic :=
    eval₂_cyclotomic_twentyNine_eq_zero t ht ht_ne_one
  calc
    (t - 1) * weightedUEval t =
        Polynomial.eval₂ (Int.castRingHom K) t
          ((X - 1) * sectionTwoUPolynomial) := by
      simp [weightedUEval]
    _ = Polynomial.eval₂ (Int.castRingHom K) t
          (Polynomial.cyclotomic 29 ℤ - C 29) := by
      rw [X_sub_one_mul_sectionTwoUPolynomial]
    _ = -(29 : K) := by simp [hcyclotomic]

/-- **The inverse identity displayed in the paper.**  If `29` is nonzero in
the target field, then
`(t-1)⁻¹ = -U(t)/29` for every nontrivial twenty-ninth root `t`. -/
theorem sub_one_inv_eq_neg_weightedUEval_div_twentyNine
    {K : Type*} [Field K] (t : K)
    (ht : t ^ 29 = 1) (ht_ne_one : t ≠ 1)
    (h29 : (29 : K) ≠ 0) :
    (t - 1)⁻¹ = -weightedUEval t / (29 : K) := by
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht_ne_one
  apply (mul_eq_one_iff_inv_eq₀ hden).mp
  calc
    (t - 1) * (-weightedUEval t / (29 : K)) =
        (-((t - 1) * weightedUEval t)) / (29 : K) := by
      ring
    _ = (-(-(29 : K))) / (29 : K) := by
      rw [sub_one_mul_weightedUEval t ht ht_ne_one]
    _ = 1 := by simp [h29]

/-- The preceding identity at the paper's standard complex root and every
nonzero exponent modulo `29`. -/
theorem zeta29_pow_sub_one_inv
    (e : Z29) (he : e ≠ 0) :
    (zeta29 ^ e.val - 1)⁻¹ =
      -weightedUEval (zeta29 ^ e.val) / (29 : ℂ) := by
  have ht : (zeta29 ^ e.val) ^ 29 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      zeta29_pow_twentyNine, one_pow]
  have ht_ne_one : zeta29 ^ e.val ≠ 1 :=
    zeta29_pow_ne_one
      (Nat.not_dvd_of_pos_of_lt (ZMod.val_pos.mpr he) e.val_lt)
  exact sub_one_inv_eq_neg_weightedUEval_div_twentyNine
    (zeta29 ^ e.val) ht ht_ne_one (by norm_num)

/-! ## Generic `ZMod q` specialization -/

/-- Exact order `29` supplies the twenty-ninth-root equation. -/
theorem zmod_pow_twentyNine_eq_one_of_order_twentyNine
    {q : ℕ} (w : ZMod q) (horder : orderOf w = 29) :
    w ^ 29 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  simp [horder]

/-- Exact order `29` and a nonzero residue exponent supply the denominator
condition needed for the field quotient.  This statement does not require
`q` to be prime. -/
theorem zmod_pow_sub_one_ne_zero_of_order_twentyNine
    {q : ℕ} (w : ZMod q) (horder : orderOf w = 29)
    (e : Z29) (he : e ≠ 0) :
    w ^ e.val - 1 ≠ 0 := by
  intro hzero
  have hpow : w ^ e.val = 1 := sub_eq_zero.mp hzero
  have hdvd : 29 ∣ e.val := by
    have hdvdOrder : orderOf w ∣ e.val :=
      (orderOf_dvd_iff_pow_eq_one).2 hpow
    simpa only [horder] using hdvdOrder
  have hval : e.val = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd e.val_lt
  exact he ((ZMod.val_eq_zero e).mp hval)

/-- Exponent reduction modulo `29` for any chosen twenty-ninth root. -/
private theorem root_pow_zmod_mul
    {q : ℕ} (w : ZMod q) (hw : w ^ 29 = 1)
    (e : Z29) (s : Fin 28) :
    w ^ (e * (s.val : Z29)).val =
      (w ^ e.val) ^ s.val := by
  symm
  calc
    (w ^ e.val) ^ s.val = w ^ (e.val * s.val) :=
      (pow_mul w e.val s.val).symm
    _ = w ^ ((e.val * s.val) % 29) :=
      pow_eq_pow_mod (e.val * s.val) hw
    _ = w ^ (e * (s.val : Z29)).val := by
      rw [ZMod.val_mul,
        ZMod.val_natCast_of_lt
          (s.isLt.trans (by norm_num : 28 < 29))]

/-- Evaluation of the cyclic representative `U e` is the scalar polynomial
`U(w^e)`.  This is the finite-ring counterpart of
`cyclicToPolynomialQuotient_U`. -/
theorem evalRoot_U_eq_weightedUEval
    (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1) (e : Z29) :
    evalRoot q w hw (U e) = weightedUEval (w ^ e.val) := by
  rw [U, map_sum, weightedUEval_eq_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [evalRoot_monomial_pow]
  exact congrArg
    (fun x : ZMod q => ((28 - (s.val : ℤ) : ℤ) : ZMod q) * x)
    (root_pow_zmod_mul w hw e s)

/-- The weighted polynomial entry specializes to the literal quotient entry.
The denominator hypothesis is stated explicitly. -/
theorem evalRoot_paperEntry_eq_scaled_literalREntry
    {q : ℕ} [Fact (Nat.Prime q)]
    (w : ZMod q) (hw : w ^ 29 = 1)
    (e : Z29) (hden : w ^ e.val - 1 ≠ 0) :
    evalRoot q w hw (paperEntry e) =
      (29 : ZMod q) * literalREntry q w e := by
  let t : ZMod q := w ^ e.val
  have ht : t ^ 29 = 1 := by
    dsimp [t]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hw, one_pow]
  have ht_ne_one : t ≠ 1 := by
    exact sub_ne_zero.mp hden
  change evalRoot q w hw
      (CyclotomicCertificate.monomial 0 29 - 2 • U e) =
    (29 : ZMod q) * ((t + 1) / (t - 1))
  calc
    evalRoot q w hw
        (CyclotomicCertificate.monomial 0 29 - 2 • U e) =
        (29 : ZMod q) - 2 * weightedUEval t := by
      rw [map_sub, map_nsmul, evalRoot_monomial_pow,
        evalRoot_U_eq_weightedUEval]
      simp [t]
    _ = (29 : ZMod q) * ((t + 1) / (t - 1)) := by
      rw [← mul_div_assoc, eq_div_iff (sub_ne_zero.mpr ht_ne_one)]
      calc
        ((29 : ZMod q) - 2 * weightedUEval t) * (t - 1) =
            29 * (t - 1) -
              2 * ((t - 1) * weightedUEval t) := by ring
        _ = 29 * (t + 1) := by
          rw [sub_one_mul_weightedUEval t ht ht_ne_one]
          ring

/-- The generic finite-field inverse formula, with all arithmetic
hypotheses visible. -/
theorem finiteField_pow_sub_one_inv
    {q : ℕ} [Fact (Nat.Prime q)]
    (w : ZMod q) (horder : orderOf w = 29)
    (h29 : (29 : ZMod q) ≠ 0)
    (e : Z29) (he : e ≠ 0) :
    (w ^ e.val - 1)⁻¹ =
      -weightedUEval (w ^ e.val) / (29 : ZMod q) := by
  have hw := zmod_pow_twentyNine_eq_one_of_order_twentyNine w horder
  have hden :=
    zmod_pow_sub_one_ne_zero_of_order_twentyNine w horder e he
  have ht : (w ^ e.val) ^ 29 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hw, one_pow]
  exact sub_one_inv_eq_neg_weightedUEval_div_twentyNine
    (w ^ e.val) ht (sub_ne_zero.mp hden) h29

/-- **Generic finite-field entry specialization.**  For every prime modulus
`q`, every order-`29` element `w`, and every nonzero exponent `e`, the
integral cyclotomic entry specializes to `29` times the literal quotient
entry.  The nonvanishing of `29` is retained explicitly because it is the
condition used by the inverse formula and by later cancellation steps. -/
theorem scalarEntry_eq_scaled_literalREntry_of_order_twentyNine
    {q : ℕ} [Fact (Nat.Prime q)]
    (w : ZMod q) (horder : orderOf w = 29)
    (_h29 : (29 : ZMod q) ≠ 0)
    (e : Z29) (he : e ≠ 0) :
    scalarEntry q w e =
      (29 : ZMod q) * literalREntry q w e := by
  let hw : w ^ 29 = 1 :=
    zmod_pow_twentyNine_eq_one_of_order_twentyNine w horder
  have hden : w ^ e.val - 1 ≠ 0 :=
    zmod_pow_sub_one_ne_zero_of_order_twentyNine w horder e he
  have hw_ne_one : w ≠ 1 := by
    intro hw_one
    subst w
    norm_num at horder
  have hpowerSum : ∑ a : Z29, w ^ a.val = 0 := by
    change ∑ a : Fin 29, w ^ a.val = 0
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hw_ne_one, hw]
    norm_num
  have hcyclotomic : evalRoot q w hw cyclotomicSum = 0 :=
    evalRoot_cyclotomicSum_eq_zero q w hw hpowerSum
  calc
    scalarEntry q w e = evalRoot q w hw (entry e) :=
      (evalRoot_entry q w hw e).symm
    _ = evalRoot q w hw (paperEntry e) := by
      rw [paperEntry_eq_entry_sub_cyclotomicSum e he,
        map_sub, map_zsmul, hcyclotomic]
      simp
    _ = (29 : ZMod q) * literalREntry q w e :=
      evalRoot_paperEntry_eq_scaled_literalREntry w hw e hden

end
end LocalizationBridge
end SunCotangent
