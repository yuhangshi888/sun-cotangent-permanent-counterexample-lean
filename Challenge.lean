import Mathlib

/-!
# The `p = 29` cotangent-permanent counterexample

This is the deliberately small statement surface submitted to Palomar. It
uses only ordinary Mathlib definitions and spells out the matrix in full.
The two `sorry`s are Palomar's designated Challenge holes; the corresponding
declarations in `Solution.lean` are proved by the zero-`sorry` development.
The explicit `letI` binders pin the standard finite instance and the prime
fact, making the exported statement independent of the surrounding imports.
-/

namespace SunCotangentP29

/-- The normalized cotangent permanent at `p = 29` has the displayed exact
integer value. -/
theorem cotangentPermanent29_exact :
    Real.sqrt 29 *
        (letI : Fintype (Fin 14) := Fin.fintype 14
         Matrix.permanent
           (fun j k : Fin 14 ↦
             Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29))) =
      84_643_985_981_440 := by
  sorry

/-- At `p = 29`, the sign in the cotangent inequality of Sun's
Conjecture 4.7(ii) is reversed. -/
theorem sunSignCounterexample :
    (letI : Fact (Nat.Prime 29) := ⟨by decide⟩
     (legendreSym 29 (-1) : ℝ) *
         (Real.sqrt 29 *
           (letI : Fintype (Fin 14) := Fin.fintype 14
            Matrix.permanent
              (fun j k : Fin 14 ↦
                Real.cot (Real.pi * ((j.val + 1) * (k.val + 1)) / 29)))) > 0) := by
  sorry

end SunCotangentP29
