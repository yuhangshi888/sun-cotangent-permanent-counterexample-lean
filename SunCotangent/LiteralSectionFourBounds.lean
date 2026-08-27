import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import SunCotangent.LiteralCyclotomicCertificate

/-!
# Literal polynomial identity and lifting bounds from Sections 2 and 4

This file records the weighted polynomial `U` exactly as it is printed in
the paper and proves its elementary telescoping identity.  It then carries
out the coefficient lifting estimate for the literal, uncentered Section 4
certificate.  In particular, the bound below does not pass through the
antisymmetric representatives used by the modular computation.
-/

open scoped BigOperators

namespace SunCotangent
namespace LiteralSectionFourBounds

open Polynomial
open CyclotomicCertificate

noncomputable section

local instance primeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-! ## The weighted polynomial from Section 2 -/

/-- The polynomial `U(X) = ∑_(s=0)^27 (28-s) X^s` used in the paper. -/
def sectionTwoUPolynomial : ℤ[X] :=
  ∑ s : Fin 28,
    C (28 - (s.val : ℤ)) * X ^ s.val

/-- The telescoping identity behind
`29 - 2 U(ζ) = 29 (ζ + 1) / (ζ - 1)` at a nontrivial
twenty-ninth root of unity. -/
theorem X_sub_one_mul_sectionTwoUPolynomial :
    (X - 1) * sectionTwoUPolynomial =
      Polynomial.cyclotomic 29 ℤ - C 29 := by
  rw [Polynomial.cyclotomic_prime]
  norm_num [sectionTwoUPolynomial, Fin.sum_univ_succ,
    Finset.sum_range_succ]
  ; ring

/-! ## Literal cyclic representatives -/

/-- The square-counting Gauss polynomial has coefficientwise `ℓ¹` norm
exactly `29`: every one of the twenty-nine square indices contributes once,
including the index zero. -/
theorem gaussSquares_cyclicL1_eq :
    CyclotomicBounds.cyclicL1 gaussSquares = 29 := by
  unfold CyclotomicBounds.cyclicL1
  simp only [gaussSquares_coeff]
  decide +kernel

/-- The triangle-inequality estimate for the literal weighted sum.  It is
uniform in the exponent, so it remains valid even when powers collide. -/
theorem U_cyclicL1_le (e : Z29) :
    CyclotomicBounds.cyclicL1 (U e) ≤ 406 := by
  unfold U
  calc
    CyclotomicBounds.cyclicL1
        (∑ s : Fin 28,
          CyclotomicCertificate.monomial
            (e * (s.val : Z29)) (28 - (s.val : ℤ))) ≤
        ∑ s : Fin 28,
          CyclotomicBounds.cyclicL1
            (CyclotomicCertificate.monomial
              (e * (s.val : Z29)) (28 - (s.val : ℤ))) := by
      simpa using CyclotomicBounds.cyclicL1_finset_sum_le
        (Finset.univ : Finset (Fin 28))
        (fun s ↦
          CyclotomicCertificate.monomial
            (e * (s.val : Z29)) (28 - (s.val : ℤ)))
    _ = ∑ s : Fin 28, |28 - (s.val : ℤ)| := by
      apply Finset.sum_congr rfl
      intro s _hs
      simpa [CyclotomicCertificate.monomial] using
        CyclotomicBounds.cyclicL1_single
          (e * (s.val : Z29)) (28 - (s.val : ℤ))
    _ = 406 := by
      norm_num [Fin.sum_univ_succ]

private theorem cyclicL1_two_nsmul_le (f : Cyclic ℤ) :
    CyclotomicBounds.cyclicL1 (2 • f) ≤
      2 * CyclotomicBounds.cyclicL1 f := by
  simpa [two_nsmul, two_mul] using
    CyclotomicBounds.cyclicL1_add_le f f

/-- Every literal entry `29 - 2 U(X^e)` has `ℓ¹` norm at most
`29²`.  The nonzero hypothesis is the one satisfied by every exponent in
the paper's `14 × 14` matrix; the estimate itself is uniform. -/
theorem paperEntry_cyclicL1_le (e : Z29) (_he : e ≠ 0) :
    CyclotomicBounds.cyclicL1 (paperEntry e) ≤ (29 : ℤ) ^ 2 := by
  calc
    CyclotomicBounds.cyclicL1 (paperEntry e) =
        CyclotomicBounds.cyclicL1
          (CyclotomicCertificate.monomial 0 29 - 2 • U e) := rfl
    _ ≤ CyclotomicBounds.cyclicL1
          (CyclotomicCertificate.monomial 0 29) +
          CyclotomicBounds.cyclicL1 (2 • U e) :=
      CyclotomicBounds.cyclicL1_sub_le _ _
    _ = 29 + CyclotomicBounds.cyclicL1 (2 • U e) := by
      simp [CyclotomicCertificate.monomial]
    _ ≤ 29 + 2 * CyclotomicBounds.cyclicL1 (U e) :=
      add_le_add_right (cyclicL1_two_nsmul_le (U e)) 29
    _ ≤ 29 + 2 * 406 := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (U_cyclicL1_le e)
          (show (0 : ℤ) ≤ 2 by norm_num)) 29
    _ = (29 : ℤ) ^ 2 := by norm_num

/-- The entrywise bound for the literal Section 4 matrix. -/
theorem literalCyclotomicMatrix_entry_cyclicL1_le (i j : Fin 14) :
    CyclotomicBounds.cyclicL1 (literalCyclotomicMatrix i j) ≤
      (29 : ℤ) ^ 2 := by
  simpa [literalCyclotomicMatrix] using
    paperEntry_cyclicL1_le _
      (literalMatrix_exponent_ne_zero i j)

/-- The permanent part of the literal certificate contributes the factor
`14! (29²)^14`. -/
theorem literalCyclotomicPermanent_cyclicL1_le :
    CyclotomicBounds.cyclicL1
        (Matrix.permanent literalCyclotomicMatrix) ≤
      (Nat.factorial 14 : ℤ) * ((29 : ℤ) ^ 2) ^ 14 := by
  apply CyclotomicBounds.permanent_cyclicL1_le
    literalCyclotomicMatrix ((29 : ℤ) ^ 2)
  intro i j
  exact literalCyclotomicMatrix_entry_cyclicL1_le i j

/-- The literal, uncentered left side of equation (4.1), before passing to
the cyclotomic quotient. -/
def literalCertificateCyclic : Cyclic ℤ :=
  gaussSquares * Matrix.permanent literalCyclotomicMatrix

/-- The integral lifting bound printed in Section 4. -/
def sectionFourLiftingBound : ℤ :=
  (Nat.factorial 14 : ℤ) * 29 ^ 29

theorem sectionFourLiftingBound_eq_broadCertificateBound :
    sectionFourLiftingBound =
      CyclotomicBounds.broadCertificateBound := by
  rfl

/-- The literal certificate has `ℓ¹` norm at most
`B = 14! · 29^29`. -/
theorem literalCertificateCyclic_cyclicL1_le :
    CyclotomicBounds.cyclicL1 literalCertificateCyclic ≤
      sectionFourLiftingBound := by
  calc
    CyclotomicBounds.cyclicL1 literalCertificateCyclic ≤
        CyclotomicBounds.cyclicL1 gaussSquares *
          CyclotomicBounds.cyclicL1
            (Matrix.permanent literalCyclotomicMatrix) := by
      exact CyclotomicBounds.cyclicL1_mul_le _ _
    _ = 29 * CyclotomicBounds.cyclicL1
          (Matrix.permanent literalCyclotomicMatrix) := by
      rw [gaussSquares_cyclicL1_eq]
    _ ≤ 29 *
          ((Nat.factorial 14 : ℤ) * ((29 : ℤ) ^ 2) ^ 14) := by
      exact mul_le_mul_of_nonneg_left
        literalCyclotomicPermanent_cyclicL1_le (by norm_num)
    _ = sectionFourLiftingBound := by
      norm_num [sectionFourLiftingBound, Nat.factorial]

/-! ## Canonical lifted coefficients -/

/-- The twenty-eight coefficients after subtracting the coefficient of
`X^28`, exactly as in the paper's passage from the cyclic presentation to
degree at most `27`. -/
def canonicalCoeff (f : Cyclic ℤ) (i : Fin 28) : ℤ :=
  f.coeff ((i.val : ℕ) : Z29) - f.coeff (28 : Z29)

private theorem canonicalIndex_ne_twentyEight (i : Fin 28) :
    ((i.val : ℕ) : Z29) ≠ (28 : Z29) := by
  revert i
  decide +kernel

/-- Subtracting the `X^28` coefficient cannot cost more than the whole
coefficientwise `ℓ¹` norm. -/
theorem canonicalCoeff_abs_le_cyclicL1 (f : Cyclic ℤ) (i : Fin 28) :
    |canonicalCoeff f i| ≤ CyclotomicBounds.cyclicL1 f := by
  unfold canonicalCoeff
  exact CyclotomicBounds.abs_coeff_sub_coeff_le_cyclicL1
    f ((i.val : ℕ) : Z29) (28 : Z29)
      (canonicalIndex_ne_twentyEight i)

/-- The literal coefficient lifting estimate used in equation (4.2): every
canonical coefficient lies in the interval `[-B, B]`. -/
theorem canonicalCoeff_literalCertificateCyclic_abs_le (i : Fin 28) :
    |canonicalCoeff literalCertificateCyclic i| ≤
      sectionFourLiftingBound := by
  exact (canonicalCoeff_abs_le_cyclicL1
    literalCertificateCyclic i).trans
      literalCertificateCyclic_cyclicL1_le

end
end LiteralSectionFourBounds
end SunCotangent
