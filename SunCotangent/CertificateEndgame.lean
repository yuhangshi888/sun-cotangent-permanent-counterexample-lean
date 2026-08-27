import Mathlib.NumberTheory.LegendreSymbol.Basic
import SunCotangent.CertificateCRT
import SunCotangent.CertificateComplexBridge
import SunCotangent.EagerModPack

/-!
# Endgame from the finite certificate to the cotangent counterexample

This module contains only exact transport.  Its single finite hypothesis is
the strict six-component permanent equality supplied by the closed evaluator.
-/

namespace SunCotangent

open CyclotomicCertificate

local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

private theorem claimedCertificateInteger_eq_certificateInteger :
    CyclotomicBounds.claimedCertificateInteger = certificateInteger := rfl

/-- The one strict-product permanent certificate implies the exact real
cotangent-permanent value. -/
theorem real_cotangentPermanent29_value_of_eagerCertificate
    (heager :
      Matrix.permanent eagerPackMatrix = expectedEagerPermanent) :
    Real.sqrt 29 * realCotMatrix29.permanent = 84643985981440 := by
  apply real_cotangentPermanent29_value_of_certificate
  apply CertificateComplexBridge.complex_certificate_of_canonicalConstant
  rw [← claimedCertificateInteger_eq_certificateInteger]
  exact CertificateCRT.canonicalConstant_eq_claimed
    (packPermanent_of_eagerPermanent heager)

/-- The Legendre symbol occurring in Sun's proposed sign law is positive at
`p = 29`. -/
theorem legendreSym_neg_one_twentyNine : legendreSym 29 (-1) = 1 := by
  rw [legendreSym.at_neg_one (by norm_num)]
  norm_num [ZMod.χ₄_nat_eq_if_mod_four]

/-- The exact value has the opposite sign from the proposed inequality at
`p = 29`. -/
theorem sun_cotangent_sign_counterexample_of_eagerCertificate
    (heager :
      Matrix.permanent eagerPackMatrix = expectedEagerPermanent) :
    (legendreSym 29 (-1) : ℝ) *
        (Real.sqrt 29 * realCotMatrix29.permanent) > 0 := by
  rw [legendreSym_neg_one_twentyNine]
  norm_num [real_cotangentPermanent29_value_of_eagerCertificate heager]

end SunCotangent
