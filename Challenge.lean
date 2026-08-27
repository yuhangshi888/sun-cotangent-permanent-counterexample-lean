import Mathlib

/-!
# The `p = 29` cotangent-permanent counterexample

This is the deliberately small statement surface submitted to Palomar. It
uses only ordinary Mathlib definitions and spells out the matrix in full.
The two `sorry`s are Palomar's designated Challenge holes; the corresponding
declarations in `Solution.lean` are proved by the zero-`sorry` development.
-/

namespace SunCotangentP29

local instance challengePrimeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- The normalized cotangent permanent at `p = 29` has the displayed exact
integer value. -/
theorem cotangentPermanent29_exact :
    Real.sqrt 29 *
        Matrix.permanent
          (fun j k : Fin 14 ↦
            Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29)) =
      84_643_985_981_440 := by
  sorry

/-- At `p = 29`, the sign in the cotangent inequality of Sun's
Conjecture 4.7(ii) is reversed. -/
theorem sunSignCounterexample :
    (legendreSym 29 (-1) : ℝ) *
        (Real.sqrt 29 *
          Matrix.permanent
            (fun j k : Fin 14 ↦
              Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29))) > 0 := by
  sorry

end SunCotangentP29
