import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Fin
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.NormNum
import SunCotangent.PermanentDP

/-!
# A kernel-efficient bitmask presentation of the 14 by 14 Ryser sum

`Finset.powerset` is mathematically convenient but expensive to normalize in
a closed kernel computation.  This file proves once and for all that scanning
the natural masks `0,...,2^14-1` gives exactly the same Ryser expression.
-/

open scoped BigOperators

namespace SunCotangent
namespace CyclotomicBitmask

/-- The subset of `Fin 14` encoded by the low fourteen bits of `mask`. -/
def maskSubset (mask : Fin (2 ^ 14)) : Finset (Fin 14) :=
  Finset.univ.filter fun i ↦ mask.val.testBit i.val

/-- The ordinary binary encoding of a subset of `Fin 14`. -/
def subsetMaskVal (s : Finset (Fin 14)) : ℕ :=
  ∑ i ∈ s, 2 ^ i.val

private theorem subsetMaskVal_lt (s : Finset (Fin 14)) :
    subsetMaskVal s < 2 ^ 14 := by
  calc
    subsetMaskVal s ≤ ∑ i : Fin 14, 2 ^ i.val := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ = 2 ^ 14 - 1 := by decide +kernel
    _ < 2 ^ 14 := by norm_num

/-- A subset, encoded as its bounded fourteen-bit natural number. -/
def subsetMask (s : Finset (Fin 14)) : Fin (2 ^ 14) :=
  ⟨subsetMaskVal s, subsetMaskVal_lt s⟩

private theorem bitIndices_bounded (mask : Fin (2 ^ 14))
    (i : ℕ) (hi : i ∈ mask.val.bitIndices.toFinset) : i < 14 := by
  have hpow : 2 ^ i ≤ mask.val :=
    Nat.two_pow_le_of_mem_bitIndices (by simpa using hi)
  by_contra h
  have h14i : 14 ≤ i := Nat.le_of_not_gt h
  have hmono : 2 ^ 14 ≤ 2 ^ i :=
    Nat.pow_le_pow_right (by norm_num) h14i
  exact (not_lt_of_ge (hmono.trans hpow)) mask.isLt

private theorem maskSubset_eq_attachFin (mask : Fin (2 ^ 14)) :
    maskSubset mask = mask.val.bitIndices.toFinset.attachFin
      (bitIndices_bounded mask) := by
  ext i
  simp [maskSubset, Nat.mem_bitIndices]

private theorem maskSubset_subsetMask (s : Finset (Fin 14)) :
    maskSubset (subsetMask s) = s := by
  apply Finset.map_injective Fin.valEmbedding
  rw [maskSubset_eq_attachFin, Finset.map_valEmbedding_attachFin]
  change (subsetMaskVal s).bitIndices.toFinset = s.map Fin.valEmbedding
  simpa [subsetMaskVal] using
    (Finset.toFinset_bitIndices_sum_two_pow (s.map Fin.valEmbedding))

private theorem sum_attachFin_val (s : Finset ℕ) {n : ℕ}
    (h : ∀ m ∈ s, m < n) (f : ℕ → ℕ) :
    (∑ i ∈ s.attachFin h, f i.val) = ∑ m ∈ s, f m := by
  refine Finset.sum_bij (fun i _ ↦ i.val) ?_ ?_ ?_ ?_
  · intro i hi
    exact (Finset.mem_attachFin h).mp hi
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro m hm
    let i : Fin n := ⟨m, h m hm⟩
    exact ⟨i, (Finset.mem_attachFin h).mpr hm, rfl⟩
  · intro i _
    rfl

private theorem subsetMask_maskSubset (mask : Fin (2 ^ 14)) :
    subsetMask (maskSubset mask) = mask := by
  apply Fin.ext
  change subsetMaskVal (maskSubset mask) = mask.val
  rw [maskSubset_eq_attachFin]
  unfold subsetMaskVal
  rw [sum_attachFin_val]
  exact Finset.sum_toFinset_bitIndices_two_pow mask.val

/-- Binary masks are explicitly equivalent to all subsets of `Fin 14`. -/
def maskEquivSubset : Fin (2 ^ 14) ≃ Finset (Fin 14) where
  toFun := maskSubset
  invFun := subsetMask
  left_inv := subsetMask_maskSubset
  right_inv := maskSubset_subsetMask

/-- Ryser's formula scanned in increasing binary-mask order. -/
def bitmaskRyser {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) : R :=
  ∑ mask : Fin (2 ^ 14),
    (-1 : R) ^ (maskSubset mask).card *
      ∏ j : Fin 14, ∑ i : Fin 14,
        if mask.val.testBit i.val then 0 else M i j

/-- The bitmask scan is exactly the generic, proved Ryser formula. -/
theorem bitmaskRyser_eq_ryser {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    bitmaskRyser M = SunCotangent.ryserPermanent M := by
  classical
  unfold bitmaskRyser SunCotangent.ryserPermanent
  refine Finset.sum_bij (fun mask _ ↦ maskSubset mask) ?_ ?_ ?_ ?_
  · intro mask _
    simp
  · intro a _ b _ hab
    exact maskEquivSubset.injective hab
  · intro s hs
    refine ⟨subsetMask s, Finset.mem_univ _, ?_⟩
    exact maskSubset_subsetMask s
  · intro mask _
    congr 2
    funext j
    have hset : (Finset.univ \ maskSubset mask : Finset (Fin 14)) =
        Finset.univ.filter (fun i ↦ ¬mask.val.testBit i.val) := by
      ext i
      simp [maskSubset]
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : mask.val.testBit i.val <;> simp [h]

/-- Hence the bitmask evaluator computes Mathlib's permanent. -/
theorem bitmaskRyser_eq_permanent {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    bitmaskRyser M = Matrix.permanent M := by
  rw [bitmaskRyser_eq_ryser, SunCotangent.ryserPermanent_eq_permanent]

end CyclotomicBitmask
end SunCotangent
