import SunCotangent.OriginalCyclotomicModuli

/-!
# Coefficient lifting for the original Section 4 certificate

This file isolates the CRT lifting direction used in Section 4 of the paper.
It does not assume the final integral certificate, or any equality involving
`canonicalConstant`.  The input is exactly the output of the original
coefficientwise modular computations: vanishing of each difference
coefficient in the three residue rings.
-/

namespace SunCotangent
namespace CyclotomicLifting

open LiteralSectionFourBounds
open OriginalCyclotomicModuli

/-! ## A generic three-modulus lifting lemma -/

/-- If an integer vanishes modulo three pairwise-coprime natural moduli and
lies in an interval shorter than their product, then it is zero.

The deliberately symmetric hypothesis
`m₁m₂m₃ > 2 * (B + E)` is the form used in Section 4.  The coefficient
hypothesis `|d| ≤ B + E` is already stronger than what is needed for the
last step, but retaining the factor `2` records the paper's centered
lifting criterion exactly. -/
theorem eq_zero_of_three_zmod
    (m₁ m₂ m₃ : ℕ) (B E d : ℤ)
    (hcoprime₁₂ : Nat.Coprime m₁ m₂)
    (hcoprime₁₃ : Nat.Coprime m₁ m₃)
    (hcoprime₂₃ : Nat.Coprime m₂ m₃)
    (hmod₁ : (d : ZMod m₁) = 0)
    (hmod₂ : (d : ZMod m₂) = 0)
    (hmod₃ : (d : ZMod m₃) = 0)
    (hbound : |d| ≤ B + E)
    (hproduct :
      (m₁ : ℤ) * (m₂ : ℤ) * (m₃ : ℤ) > 2 * (B + E)) :
    d = 0 := by
  have hdvd₁ : (m₁ : ℤ) ∣ d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hmod₁
  have hdvd₂ : (m₂ : ℤ) ∣ d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hmod₂
  have hdvd₃ : (m₃ : ℤ) ∣ d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hmod₃
  have hcoprime₁₂' : IsCoprime (m₁ : ℤ) (m₂ : ℤ) :=
    hcoprime₁₂.cast
  have hcoprime₁₃' : IsCoprime (m₁ : ℤ) (m₃ : ℤ) :=
    hcoprime₁₃.cast
  have hcoprime₂₃' : IsCoprime (m₂ : ℤ) (m₃ : ℤ) :=
    hcoprime₂₃.cast
  have hdvd₁₂ : (m₁ : ℤ) * (m₂ : ℤ) ∣ d :=
    hcoprime₁₂'.mul_dvd hdvd₁ hdvd₂
  have hdvdProduct :
      (m₁ : ℤ) * (m₂ : ℤ) * (m₃ : ℤ) ∣ d :=
    (hcoprime₁₃'.mul_left hcoprime₂₃').mul_dvd hdvd₁₂ hdvd₃
  have hd_lt_product :
      |d| < (m₁ : ℤ) * (m₂ : ℤ) * (m₃ : ℤ) := by
    linarith [abs_nonneg d]
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvdProduct
  simpa only [Int.natAbs_abs] using
    Int.natAbs_lt_natAbs_of_nonneg_of_lt (abs_nonneg d) hd_lt_product

/-! ## Specialization to the twenty-eight paper coefficients -/

/-- The absolute value of the claimed right-hand coefficient is bounded by
`E`, uniformly over the twenty-eight canonical positions. -/
private theorem paperRightHandCoeff_abs_le (i : Fin 28) :
    |if i = 0 then CyclotomicCertificate.certificateInteger else 0| ≤
      paperBoundE := by
  by_cases hi : i = 0
  · simp only [hi, if_pos]
    norm_num [paperBoundE, CyclotomicCertificate.certificateInteger]
  · simp [hi, paperBoundE]

/-- The literal `ℓ¹` estimate gives the interval needed to lift every
difference coefficient.  This bound is independent of all modular
computations and of the desired certificate equality. -/
theorem paperCanonicalDifferenceCoeff_abs_le (i : Fin 28) :
    |paperCanonicalDifferenceCoeff i| ≤ paperBoundB + paperBoundE := by
  have hleft :
      |canonicalCoeff literalCertificateCyclic i| ≤ paperBoundB := by
    rw [paperBoundB_eq_sectionFourLiftingBound]
    exact canonicalCoeff_literalCertificateCyclic_abs_le i
  rw [paperCanonicalDifferenceCoeff]
  exact (abs_sub _ _).trans
    (add_le_add hleft (paperRightHandCoeff_abs_le i))

/-- One coefficient is forced to vanish by its three original residue
certificates and the literal coefficient bound.  No final certificate
identity is used. -/
theorem paperCanonicalDifferenceCoeff_eq_zero_of_residues
    (i : Fin 28)
    (hmod₁ :
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus1) = 0)
    (hmod₂ :
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus2) = 0)
    (hmod₃ :
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus3) = 0) :
    paperCanonicalDifferenceCoeff i = 0 := by
  apply eq_zero_of_three_zmod
    paperModulus1 paperModulus2 paperModulus3
    paperBoundB paperBoundE (paperCanonicalDifferenceCoeff i)
  · exact paperModuli_isCoprime12.natCoprime
  · exact paperModuli_isCoprime13.natCoprime
  · exact paperModuli_isCoprime23.natCoprime
  · exact hmod₁
  · exact hmod₂
  · exact hmod₃
  · exact paperCanonicalDifferenceCoeff_abs_le i
  · simpa [paperModulusProduct] using
      paperModulusProduct_gt_twice_bound

/-- The coefficientwise lifting conclusion in its paper-level form: three
families of residue certificates force all twenty-eight canonical
difference coefficients to vanish over `ℤ`. -/
theorem paperCanonicalDifferenceCoeff_all_eq_zero_of_residues
    (hmod₁ : ∀ i : Fin 28,
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus1) = 0)
    (hmod₂ : ∀ i : Fin 28,
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus2) = 0)
    (hmod₃ : ∀ i : Fin 28,
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus3) = 0) :
    ∀ i : Fin 28, paperCanonicalDifferenceCoeff i = 0 := by
  intro i
  exact paperCanonicalDifferenceCoeff_eq_zero_of_residues i
    (hmod₁ i) (hmod₂ i) (hmod₃ i)

/-- Equivalently, the twenty-eight lifted coefficients of the literal left
side are exactly the canonical coefficients of the claimed constant right
side. -/
theorem paperCanonicalCoefficients_eq_of_residues
    (hmod₁ : ∀ i : Fin 28,
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus1) = 0)
    (hmod₂ : ∀ i : Fin 28,
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus2) = 0)
    (hmod₃ : ∀ i : Fin 28,
      (paperCanonicalDifferenceCoeff i : ZMod paperModulus3) = 0) :
    ∀ i : Fin 28,
      canonicalCoeff literalCertificateCyclic i =
        if i = 0 then CyclotomicCertificate.certificateInteger else 0 := by
  intro i
  exact sub_eq_zero.mp
    (paperCanonicalDifferenceCoeff_all_eq_zero_of_residues
      hmod₁ hmod₂ hmod₃ i)

end CyclotomicLifting
end SunCotangent
