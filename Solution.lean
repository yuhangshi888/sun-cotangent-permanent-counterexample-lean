import SunCotangent.AdvertisedTheorem

/-!
# Proved Palomar solution

Comparator checks that these declarations have exactly the same types as the
two declarations in `Challenge.lean`. Their proofs come from the substantive
formalization and introduce no additional assumptions.
-/

namespace SunCotangentP29

theorem cotangentPermanent29_exact :
    Real.sqrt 29 *
        (letI : Fintype (Fin 14) := Fin.fintype 14
         Matrix.permanent
           (fun j k : Fin 14 ↦
             Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29))) =
      84_643_985_981_440 := by
  change Real.sqrt 29 * SunCotangent.realCotMatrix29.permanent =
    84_643_985_981_440
  exact SunCotangent.cotangentPermanent29_exact

theorem sunSignCounterexample :
    (letI : Fact (Nat.Prime 29) := ⟨by decide⟩
     (legendreSym 29 (-1) : ℝ) *
         (Real.sqrt 29 *
           (letI : Fintype (Fin 14) := Fin.fintype 14
            Matrix.permanent
              (fun j k : Fin 14 ↦
                Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29)))) > 0) := by
  letI : Fact (Nat.Prime 29) := ⟨by decide⟩
  change
    (legendreSym 29 (-1) : ℝ) *
        (Real.sqrt 29 * SunCotangent.realCotMatrix29.permanent) > 0
  exact SunCotangent.sun_cotangent_sign_counterexample

end SunCotangentP29
