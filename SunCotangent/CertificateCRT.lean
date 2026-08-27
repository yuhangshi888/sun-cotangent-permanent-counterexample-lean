import SunCotangent.ModularCertificates

/-!
# CRT closure of the cyclotomic certificate

This module contains no closed permanent computation.  Its sole hypothesis is
the six-component permanent equality exported by the finite evaluator.  The
argument projects that equality to the six residue rings, transports each
component through the exact cyclotomic evaluation bridge, and applies the
proved coefficient bound and CRT uniqueness theorem.
-/

namespace SunCotangent
namespace CertificateCRT

open CyclotomicCertificate

private theorem certificateInteger_eq_claimed :
    certificateInteger = CyclotomicBounds.claimedCertificateInteger := rfl

/-- A certified value of the single six-component permanent closes the
integral cyclotomic certificate unconditionally. -/
theorem canonicalConstant_eq_claimed
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    canonicalConstant = CyclotomicBounds.claimedCertificateInteger := by
  apply CyclotomicBounds.eq_claimed_of_six_zmod canonicalConstant
    canonicalConstant_abs_le
  · change (canonicalConstant : ZMod q1) =
      (CyclotomicBounds.claimedCertificateInteger : ZMod q1)
    rw [← certificateInteger_eq_claimed]
    exact canonicalConstant_mod1_of_permanent (permanent1_of_pack hpack)
  · change (canonicalConstant : ZMod q2) =
      (CyclotomicBounds.claimedCertificateInteger : ZMod q2)
    rw [← certificateInteger_eq_claimed]
    exact canonicalConstant_mod2_of_permanent (permanent2_of_pack hpack)
  · change (canonicalConstant : ZMod q3) =
      (CyclotomicBounds.claimedCertificateInteger : ZMod q3)
    rw [← certificateInteger_eq_claimed]
    exact canonicalConstant_mod3_of_permanent (permanent3_of_pack hpack)
  · change (canonicalConstant : ZMod q4) =
      (CyclotomicBounds.claimedCertificateInteger : ZMod q4)
    rw [← certificateInteger_eq_claimed]
    exact canonicalConstant_mod4_of_permanent (permanent4_of_pack hpack)
  · change (canonicalConstant : ZMod q5) =
      (CyclotomicBounds.claimedCertificateInteger : ZMod q5)
    rw [← certificateInteger_eq_claimed]
    exact canonicalConstant_mod5_of_permanent (permanent5_of_pack hpack)
  · change (canonicalConstant : ZMod q6) =
      (CyclotomicBounds.claimedCertificateInteger : ZMod q6)
    rw [← certificateInteger_eq_claimed]
    exact canonicalConstant_mod6_of_permanent (permanent6_of_pack hpack)

end CertificateCRT
end SunCotangent
