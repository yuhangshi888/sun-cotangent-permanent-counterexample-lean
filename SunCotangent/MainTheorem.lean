import SunCotangent.AdvertisedTheorem
import SunCotangent.GrayPermanentCheckpointsCompact
import SunCotangent.CertificateEndgame
import SunCotangent.PolynomialQuotientCertificate
import SunCotangent.LiteralSectionFourBounds
import SunCotangent.OriginalCyclotomicModuli
import SunCotangent.CyclotomicLifting
import SunCotangent.LocalizationBridge
import SunCotangent.SectionThreeEndgame

/-!
# The unconditional `p = 29` cotangent-permanent counterexample

The advertised exact value and sign theorem come from the independent
three-scalar Section 4 certificate.  This full module additionally retains the
alternate six-small-modulus Gray certificate, the principal claims of Sections
3 and 4, and the independent Section 3 reconstruction with Sun's integrality
assertion kept as an explicit input.
-/

namespace SunCotangent

open scoped BigOperators

open CyclotomicCertificate

local instance mainPrimeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩
local instance mainQ1PrimeFact : Fact (Nat.Prime q1) :=
  ⟨ScalarFiniteFieldCertificate.q1_prime⟩
local instance mainQ2PrimeFact : Fact (Nat.Prime q2) :=
  ⟨ScalarFiniteFieldCertificate.q2_prime⟩
local instance mainQ3PrimeFact : Fact (Nat.Prime q3) :=
  ⟨ScalarFiniteFieldCertificate.q3_prime⟩

private theorem kernelEager :
    Matrix.permanent eagerPackMatrix = expectedEagerPermanent :=
  permanent_eagerPackMatrix_compact

private theorem kernelPack :
    Matrix.permanent packMatrix = expectedPermanentPack :=
  packPermanent_of_eagerPermanent kernelEager

private theorem kernelCanonical :
    canonicalConstant = certificateInteger := by
  change canonicalConstant = CyclotomicBounds.claimedCertificateInteger
  exact CertificateCRT.canonicalConstant_eq_claimed kernelPack

/-! ## Alternate six-small-modulus certificate -/

/-- The canonical integer equality obtained from the six-small-modulus CRT. -/
theorem canonicalConstant_eq_certificateInteger_sixSmall :
    canonicalConstant = certificateInteger :=
  kernelCanonical

/-- The exact normalized value obtained from the six-small-modulus certificate. -/
theorem tPrime29_eq_sixSmall : tPrime29 = 84_643_985_981_440 := by
  simpa only [tPrime29] using
    real_cotangentPermanent29_value_of_eagerCertificate kernelEager

/-- Direct matrix form of the alternate six-small-modulus exact value. -/
theorem cotangentPermanent29_exact_sixSmall :
    Real.sqrt 29 *
        Matrix.permanent
          (fun j k : Fin 14 ↦
            Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29)) =
      84_643_985_981_440 := by
  change Real.sqrt 29 * realCotMatrix29.permanent = 84_643_985_981_440
  exact real_cotangentPermanent29_value_of_eagerCertificate kernelEager

/-- The sign counterexample obtained from the six-small-modulus certificate. -/
theorem sun_cotangent_sign_counterexample_sixSmall :
    (legendreSym 29 (-1) : ℝ) * tPrime29 > 0 := by
  simpa only [tPrime29] using
    sun_cotangent_sign_counterexample_of_eagerCertificate kernelEager

/-! ## Consequences of the advertised theorem -/

/-- The displayed exact value is positive. -/
theorem tPrime29_pos : 0 < tPrime29 := by
  rw [tPrime29_eq]
  norm_num

/-- Integrality at `p = 29`, now obtained unconditionally from the exact
formalized value. -/
theorem tPrime29_integral :
    ∃ z : ℤ, (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent := by
  refine ⟨84_643_985_981_440, ?_⟩
  simpa [tPrime29] using tPrime29_eq.symm

/-- The exact value has the independent normalization check modulo `29`. -/
theorem tPrime29_value_mod_twentyNine :
    (84_643_985_981_440 : ZMod 29) = 1 := by
  decide +kernel

/-! ## Section 3: the literal finite-field table and reconstruction -/

/-- The complete first row of Table 1. -/
theorem table1_row_one :
    ScalarFiniteFieldCertificate.literalGauss q1 w1 = (1_391_190_231 : ZMod q1) ∧
    Matrix.permanent (ScalarFiniteFieldCertificate.literalRMatrix q1 w1) =
      (1_767_907_462 : ZMod q1) ∧
    ScalarFiniteFieldCertificate.finiteTPrimeResidue q1 w1 =
      (51_284_286 : ZMod q1) := by
  exact ⟨ScalarFiniteFieldCertificate.literalGauss1_value,
    ScalarFiniteFieldCertificate.table1_permanent_q1_of_pack kernelPack,
    ScalarFiniteFieldCertificate.table1_tPrimeResidue_q1_of_scaled
      (permanent1_of_pack kernelPack)⟩

/-- The complete second row of Table 1. -/
theorem table1_row_two :
    ScalarFiniteFieldCertificate.literalGauss q2 w2 = (106_827_755 : ZMod q2) ∧
    Matrix.permanent (ScalarFiniteFieldCertificate.literalRMatrix q2 w2) =
      (1_110_131_281 : ZMod q2) ∧
    ScalarFiniteFieldCertificate.finiteTPrimeResidue q2 w2 =
      (95_468_454 : ZMod q2) := by
  exact ⟨ScalarFiniteFieldCertificate.literalGauss2_value,
    ScalarFiniteFieldCertificate.table1_permanent_q2_of_pack kernelPack,
    ScalarFiniteFieldCertificate.table1_tPrimeResidue_q2_of_scaled
      (permanent2_of_pack kernelPack)⟩

/-- The complete third row of Table 1. -/
theorem table1_row_three :
    ScalarFiniteFieldCertificate.literalGauss q3 w3 =
      (1_918_644_949 : ZMod q3) ∧
    Matrix.permanent (ScalarFiniteFieldCertificate.literalRMatrix q3 w3) =
      (1_805_872_013 : ZMod q3) ∧
    ScalarFiniteFieldCertificate.finiteTPrimeResidue q3 w3 =
      (115_105_862 : ZMod q3) := by
  exact ⟨ScalarFiniteFieldCertificate.literalGauss3_value,
    ScalarFiniteFieldCertificate.table1_permanent_q3_of_pack kernelPack,
    ScalarFiniteFieldCertificate.table1_tPrimeResidue_q3_of_scaled
      (permanent3_of_pack kernelPack)⟩

/-- The centered representative chosen in equation (3.1). -/
theorem section_three_centered_representative :
    2 * |ScalarFiniteFieldCertificate.sectionThreeN| <
      ScalarFiniteFieldCertificate.sectionThreeModulus :=
  SectionThreeEndgame.sectionThreeN_is_centered

/-- The Archimedean estimate (3.2). -/
theorem section_three_archimedean_bound :
    |Real.sqrt 29 * realCotMatrix29.permanent| <
      6 * (Nat.factorial 14 : ℝ) * ((29 : ℝ) / 3) ^ 14 :=
  ArchimedeanCertificate.abs_sqrt_twentyNine_mul_realCotMatrix29_permanent_lt

/-- The independent Section 3 route, with its sole cited input—integrality—
kept explicit. -/
theorem section_three_exact_of_integrality
    (hintegral : ∃ z : ℤ, (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent) :
    Real.sqrt 29 * realCotMatrix29.permanent = 84_643_985_981_440 :=
  SectionThreeEndgame.exact_value_of_integrality_and_eagerCertificate hintegral kernelEager

/-! ## Section 4: the literal polynomial quotient and lifting certificate -/

/-- The elementary telescoping identity for the polynomial `U`. -/
theorem section_two_U_telescoping :
    (Polynomial.X - 1) * LiteralSectionFourBounds.sectionTwoUPolynomial =
      Polynomial.cyclotomic 29 ℤ - Polynomial.C 29 :=
  LiteralSectionFourBounds.X_sub_one_mul_sectionTwoUPolynomial

/-- Equation (4.1) in the paper's actual quotient
`ℤ[X] / span {Φ₂₉}`. -/
theorem polynomial_equation_four_one :
    (∑ a : Fin 29, PolynomialQuotientCertificate.quotientX ^ (a.val ^ 2)) *
        Matrix.permanent
          (fun j k : Fin 14 ↦
            (29 : PolynomialQuotientCertificate.PolynomialCyclotomicRing) -
              2 • PolynomialQuotientCertificate.sectionFourU
                (PolynomialQuotientCertificate.quotientX ^
                  ((j.val + 1) * (k.val + 1)))) =
      ((-84_643_985_981_440 * 29 ^ 14 : ℤ) :
        PolynomialQuotientCertificate.PolynomialCyclotomicRing) :=
  PolynomialQuotientCertificate.equation_four_one kernelCanonical

/-- The equivalent equation (4.1) in the cyclic group-ring presentation. -/
theorem literal_cyclotomic_ring_certificate :
    literalQuotientGauss * Matrix.permanent literalQuotientMatrix =
      (certificateInteger : CyclotomicRing) :=
  literal_ring_certificate_of_canonicalConstant kernelCanonical

/-- The literal coefficientwise lifting bound `B = 14! * 29^29`. -/
theorem section_four_literal_lifting_bound :
    CyclotomicBounds.cyclicL1 LiteralSectionFourBounds.literalCertificateCyclic ≤
      LiteralSectionFourBounds.sectionFourLiftingBound :=
  LiteralSectionFourBounds.literalCertificateCyclic_cyclicL1_le

/-- Every one of the twenty-eight canonical lifted coefficients satisfies
the paper's bound. -/
theorem section_four_canonical_coefficient_bound (i : Fin 28) :
    |LiteralSectionFourBounds.canonicalCoeff
        LiteralSectionFourBounds.literalCertificateCyclic i| ≤
      LiteralSectionFourBounds.sectionFourLiftingBound :=
  LiteralSectionFourBounds.canonicalCoeff_literalCertificateCyclic_abs_le i

/-- The complete data of the original three-modulus Section 4 certificate. -/
theorem original_cyclotomic_modular_certificate :
    (IsCoprime (OriginalCyclotomicModuli.paperModulus1 : ℤ)
        (OriginalCyclotomicModuli.paperModulus2 : ℤ) ∧
      IsCoprime (OriginalCyclotomicModuli.paperModulus1 : ℤ)
        (OriginalCyclotomicModuli.paperModulus3 : ℤ) ∧
      IsCoprime (OriginalCyclotomicModuli.paperModulus2 : ℤ)
        (OriginalCyclotomicModuli.paperModulus3 : ℤ)) ∧
    OriginalCyclotomicModuli.paperModulusProduct =
      12_259_964_326_927_110_457_464_553_515_448_388_006_472_404_964_466_489_997 ∧
    OriginalCyclotomicModuli.paperModulusProduct >
      2 * (OriginalCyclotomicModuli.paperBoundB + OriginalCyclotomicModuli.paperBoundE) ∧
    ∀ i : Fin 28,
      (OriginalCyclotomicModuli.paperCanonicalDifferenceCoeff i :
        ZMod OriginalCyclotomicModuli.paperModulus1) = 0 ∧
      (OriginalCyclotomicModuli.paperCanonicalDifferenceCoeff i :
        ZMod OriginalCyclotomicModuli.paperModulus2) = 0 ∧
      (OriginalCyclotomicModuli.paperCanonicalDifferenceCoeff i :
        ZMod OriginalCyclotomicModuli.paperModulus3) = 0 :=
  OriginalCyclotomicModuli.paper_cyclotomic_modular_certificate kernelCanonical

end SunCotangent
