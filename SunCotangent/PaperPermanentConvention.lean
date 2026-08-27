import SunCotangent.PermanentDP
import SunCotangent.GlynnPermanent

/-!
# The paper's permanent convention

The paper writes the permanent with the row index fixed and the column index
permuted.  Mathlib fixes the column index and permutes the row index.  The two
finite sums agree because transposition preserves the permanent.

The final theorem below records the generic mathematical agreement of the
certified Ryser and Glynn formulas.  It is a correctness theorem for the two
formulas; it does not assert that any particular matrix was evaluated twice by
independent checkpoint computations.
-/

open Equiv Fintype Finset
open scoped BigOperators

namespace SunCotangent

section

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The permanent in the row-first convention used in the paper:
`sum sigma, product i, M i (sigma i)`. -/
def paperPermanent (M : Matrix n n R) : R :=
  ∑ σ : Equiv.Perm n, ∏ i : n, M i (σ i)

/-- The paper's row-first convention agrees with Mathlib's convention for
every finite square matrix over a commutative ring. -/
theorem paperPermanent_eq_permanent (M : Matrix n n R) :
    paperPermanent M = M.permanent := by
  calc
    paperPermanent M = M.transpose.permanent := by rfl
    _ = M.permanent := Matrix.permanent_transpose M

/-- The certified Ryser and normalized fixed-pivot Glynn formulas agree for
every finite square matrix whenever `twoInv` is an explicit inverse of `2`.
This is generic formula correctness, not a claim of two independent concrete
checkpoint evaluations. -/
theorem ryserPermanent_eq_glynnPermanent (twoInv : R)
    (htwo : twoInv * (2 : R) = 1) (pivot : n) (M : Matrix n n R) :
    ryserPermanent M = glynnPermanent twoInv pivot M := by
  rw [ryserPermanent_eq_permanent M,
    glynnPermanent_eq_permanent twoInv htwo pivot M]

end

end SunCotangent
