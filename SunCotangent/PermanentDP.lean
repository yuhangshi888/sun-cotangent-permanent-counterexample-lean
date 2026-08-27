import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# A certified subset evaluator for matrix permanents

This file implements Ryser's subset formula and proves, over every commutative
ring, that it agrees with `Matrix.permanent`.  The executable expression has
`2^n` subset terms rather than `n!` permutation terms.
-/

open Equiv Fintype Finset
open scoped BigOperators

namespace SunCotangent

section

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Ryser's `2^n`-term evaluator, with Mathlib's row/column convention for
`Matrix.permanent`: the subset records the omitted row indices.  This form is
particularly convenient for a direct application of inclusion-exclusion. -/
def ryserPermanent (M : Matrix n n R) : R :=
  ∑ omitted ∈ (Finset.univ : Finset n).powerset,
    (-1 : R) ^ omitted.card *
      ∏ j : n, ∑ i ∈ (Finset.univ \ omitted), M i j

/-- The functions which omit a fixed row.  Inclusion-exclusion over these
finite sets isolates exactly the surjections. -/
private def omittingFunctions (i : n) : Finset (n → n) :=
  Finset.univ.filter fun f ↦ i ∉ Finset.univ.image f

/-- Expanding a product of row sums enumerates precisely the functions whose
values lie in the allowed set. -/
private theorem prod_rowSums_eq_sum_functions (M : Matrix n n R) (allowed : Finset n) :
    (∏ j : n, ∑ i ∈ allowed, M i j) =
      ∑ f ∈ Fintype.piFinset (fun _ : n ↦ allowed), ∏ j : n, M (f j) j := by
  exact (Finset.sum_prod_piFinset allowed (fun j i ↦ M i j)).symm

/-- Intersecting the conditions that the values omit every element of `t`
gives the finite set of functions valued in the complement of `t`. -/
private theorem inf_omittingFunctions_eq_piFinset (t : Finset n) :
    t.inf omittingFunctions =
      Fintype.piFinset (fun _ : n ↦ (Finset.univ \ t : Finset n)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      ext f
      simp
  | @insert i t hi ih =>
      rw [Finset.inf_insert, ih, Finset.inf_eq_inter]
      ext f
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        omittingFunctions, Fintype.mem_piFinset, Finset.mem_sdiff,
        Finset.mem_insert]
      constructor
      · rintro ⟨hnotImage, hallowed⟩ j (hEq | hjt)
        · exact hnotImage (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hEq⟩)
        · exact hallowed j hjt
      · intro hallowed
        constructor
        · intro hImage
          obtain ⟨j, -, hEq⟩ := Finset.mem_image.mp hImage
          exact hallowed j (Or.inl hEq)
        · intro j
          exact fun hjt ↦ hallowed j (Or.inr hjt)

/-- Membership in a finite infimum of finite sets. -/
private theorem mem_finset_inf_iff {a b : Type*} [DecidableEq a] [Fintype a]
    (s : Finset b) (F : b → Finset a) (x : a) :
    x ∈ s.inf F ↔ ∀ i ∈ s, x ∈ F i := by
  simpa only [Finset.singleton_subset_iff] using
    (Finset.le_inf_iff (s := s) (f := F) (a := ({x} : Finset a)))

/-- The intersection of the complements of all omission events is precisely
the finite set of surjective self-maps. -/
private theorem inf_compl_omittingFunctions_eq_surjections :
    (Finset.univ : Finset n).inf (fun i ↦ (omittingFunctions i)ᶜ) =
      (Finset.univ : Finset (n → n)).filter Function.Surjective := by
  classical
  ext f
  simp only [mem_finset_inf_iff, Finset.mem_univ, forall_const, Finset.mem_compl,
    Finset.mem_filter, true_and, omittingFunctions, not_not]
  constructor
  · intro h y
    obtain ⟨x, -, hxy⟩ := Finset.mem_image.mp (h y)
    exact ⟨x, hxy⟩
  · intro h y
    obtain ⟨x, hxy⟩ := h y
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hxy⟩

/-- Summing over bijective self-maps is the definition of the permanent,
reindexed from functions to bundled permutations. -/
private theorem sum_bijective_functions_eq_permanent (M : Matrix n n R) :
    (∑ f ∈ (Finset.univ : Finset (n → n)).filter Function.Bijective,
      ∏ j : n, M (f j) j) = M.permanent := by
  classical
  rw [Matrix.permanent]
  symm
  refine Finset.sum_bij (fun σ _ ↦ (σ : n → n)) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact σ.bijective
  · intro σ _ τ _ h
    exact Equiv.ext fun x ↦ congrFun h x
  · intro f hf
    have hbij : Function.Bijective f := (Finset.mem_filter.mp hf).2
    refine ⟨Equiv.ofBijective f hbij, Finset.mem_univ _, ?_⟩
    rfl
  · intro σ _
    rfl

/-- **Certified Ryser formula.**  The `2^n` subset evaluator agrees exactly
with Mathlib's permutation-sum permanent for every finite index type and every
commutative ring. -/
theorem ryserPermanent_eq_permanent (M : Matrix n n R) :
    ryserPermanent M = M.permanent := by
  classical
  let weight : (n → n) → R := fun f ↦ ∏ j : n, M (f j) j
  have hIE := Finset.inclusion_exclusion_sum_inf_compl
    (s := (Finset.univ : Finset n)) omittingFunctions weight
  calc
    ryserPermanent M =
        ∑ t ∈ (Finset.univ : Finset n).powerset,
          (-1 : ℤ) ^ t.card • ∑ f ∈ t.inf omittingFunctions, weight f := by
      unfold ryserPermanent
      apply Finset.sum_congr rfl
      intro t ht
      rw [inf_omittingFunctions_eq_piFinset]
      rw [← prod_rowSums_eq_sum_functions M (Finset.univ \ t)]
      simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    _ = ∑ f ∈ (Finset.univ : Finset n).inf
          (fun i ↦ (omittingFunctions i)ᶜ), weight f := hIE.symm
    _ = ∑ f ∈ (Finset.univ : Finset (n → n)).filter
          Function.Surjective, weight f := by
      rw [inf_compl_omittingFunctions_eq_surjections]
    _ = ∑ f ∈ (Finset.univ : Finset (n → n)).filter
          Function.Bijective, weight f := by
      congr 1
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finite.surjective_iff_bijective]
    _ = M.permanent := by
      exact sum_bijective_functions_eq_permanent M

/-- Rewrite Mathlib's permanent to the certified `2^n` subset evaluator. -/
theorem permanent_eq_ryserPermanent (M : Matrix n n R) :
    M.permanent = ryserPermanent M :=
  (ryserPermanent_eq_permanent M).symm

end

end SunCotangent
