import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.FinCases
import SunCotangent.KernelPermanentDP
import SunCotangent.ModularCertificates

/-!
# A strict product representation of the six modular components

`ModPack` is a dependent function type.  This module supplies an alternative
closed-computation target whose six components are stored in a nested product.
Ring operations on this type reduce directly to constructors and projections,
so the shared permanent scan is run over one concrete product value rather
than exposed through six applications of a function-valued result.

This file contains only structural transport proofs.  It deliberately does
not ask the kernel to evaluate the permanent.
-/

namespace SunCotangent
namespace CyclotomicCertificate

/-- The same six residue rings as `ModPack`, materialized as a right-nested
product rather than a dependent function. -/
abbrev EagerModPack :=
  ZMod q1 ×
    (ZMod q2 ×
      (ZMod q3 ×
        (ZMod q4 ×
          (ZMod q5 × ZMod q6))))

/-- The six residue matrices packed entrywise into `EagerModPack`. -/
def eagerPackMatrix : Matrix (Fin 14) (Fin 14) EagerModPack :=
  fun i j ↦
    (residueMatrix1 i j,
      (residueMatrix2 i j,
        (residueMatrix3 i j,
          (residueMatrix4 i j,
            (residueMatrix5 i j, residueMatrix6 i j)))))

/-- The expected six-component permanent in strict product form. -/
def expectedEagerPermanent : EagerModPack :=
  (permanentValue1,
    (permanentValue2,
      (permanentValue3,
        (permanentValue4,
          (permanentValue5, permanentValue6)))))

/-- Forget the strict product representation and recover the existing
dependent function representation. -/
def eagerToModPack (x : EagerModPack) : ModPack
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | 3 => x.2.2.2.1
  | 4 => x.2.2.2.2.1
  | 5 => x.2.2.2.2.2

/-- Component extraction is a ring homomorphism from the nested product to
the dependent function ring. -/
def eagerToModPackHom : EagerModPack →+* ModPack where
  toFun := eagerToModPack
  map_one' := by
    funext k
    fin_cases k <;> rfl
  map_mul' x y := by
    funext k
    fin_cases k <;> rfl
  map_zero' := by
    funext k
    fin_cases k <;> rfl
  map_add' x y := by
    funext k
    fin_cases k <;> rfl

@[simp]
theorem eagerToModPack_expected :
    eagerToModPackHom expectedEagerPermanent = expectedPermanentPack := by
  funext k
  fin_cases k <;> rfl

/-- Entrywise transport of the strict product matrix is the existing
function-valued matrix. -/
theorem eagerPackMatrix_map :
    eagerPackMatrix.map eagerToModPackHom = packMatrix := by
  ext i j k
  fin_cases k <;> rfl

private theorem permanent_map_ringHom
    {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) :
    Matrix.permanent (M.map f) = f (Matrix.permanent M) := by
  classical
  simp only [Matrix.permanent, Matrix.map_apply, map_sum, map_prod]

/-- A single permanent equality in the strict product implies the exact
six-component equality expected by the existing CRT pipeline. -/
theorem packPermanent_of_eagerPermanent
    (heager :
      Matrix.permanent eagerPackMatrix = expectedEagerPermanent) :
    Matrix.permanent packMatrix = expectedPermanentPack := by
  calc
    Matrix.permanent packMatrix =
        Matrix.permanent (eagerPackMatrix.map eagerToModPackHom) := by
      rw [eagerPackMatrix_map]
    _ = eagerToModPackHom (Matrix.permanent eagerPackMatrix) :=
      permanent_map_ringHom eagerToModPackHom eagerPackMatrix
    _ = eagerToModPackHom expectedEagerPermanent :=
      congrArg eagerToModPackHom heager
    _ = expectedPermanentPack := eagerToModPack_expected

/-- Convenience form for the intended closed theorem: a computation of the
shared-array evaluator over `EagerModPack` transports to the existing CRT
hypothesis without another permanent computation. -/
theorem packPermanent_of_eagerDP
    (heager :
      KernelPermanentDP.permanentDP eagerPackMatrix = expectedEagerPermanent) :
    Matrix.permanent packMatrix = expectedPermanentPack := by
  apply packPermanent_of_eagerPermanent
  rw [← KernelPermanentDP.permanentDP_eq_permanent]
  exact heager

end CyclotomicCertificate
end SunCotangent
