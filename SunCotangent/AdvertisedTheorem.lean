import SunCotangent.ThreeScalarCyclotomicCertificate

/-!
# The advertised `p = 29` cotangent-permanent counterexample

This lightweight public theorem surface depends only on the three-scalar
Section 4 certificate, whose residue computation is independent of the
alternate six-small-modulus certificate. In particular, importing this module
does not load the six-small-modulus Gray scan used elsewhere in the full
development.
-/

namespace SunCotangent

local instance advertisedPrimeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- Sun's normalized cotangent permanent at `p = 29`. -/
noncomputable def tPrime29 : ℝ :=
  Real.sqrt 29 * realCotMatrix29.permanent

/-- **Exact value of the normalized cotangent permanent at `p = 29`.** -/
theorem tPrime29_eq : tPrime29 = 84_643_985_981_440 := by
  simpa only [tPrime29] using
    ThreeScalarCyclotomicCertificate.real_cotangentPermanent29_value_threeScalar

/-- Direct matrix form of the exact-value theorem. -/
theorem cotangentPermanent29_exact :
    Real.sqrt 29 *
        Matrix.permanent
          (fun j k : Fin 14 ↦
            Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29)) =
      84_643_985_981_440 := by
  change Real.sqrt 29 * realCotMatrix29.permanent = 84_643_985_981_440
  exact
    ThreeScalarCyclotomicCertificate.real_cotangentPermanent29_value_threeScalar

/-- The proposed sign inequality is reversed at `p = 29`. -/
theorem sun_cotangent_sign_counterexample :
    (legendreSym 29 (-1) : ℝ) * tPrime29 > 0 := by
  simpa only [tPrime29] using
    ThreeScalarCyclotomicCertificate.sun_cotangent_sign_counterexample_threeScalar

end SunCotangent
