import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic

/-!
# Glynn's sign-vector formula for the permanent

This file proves Glynn's formula with one sign fixed to `+1`.  The
unnormalized identity is valid over every commutative ring:

`glynnSum pivot M = 2 ^ (card n - 1) * Matrix.permanent M`.

Consequently, if `twoInv` is an explicitly supplied inverse of `2`, the
normalized evaluator `glynnPermanent twoInv pivot M` is exactly Mathlib's
permutation-sum permanent.  Supplying the inverse explicitly keeps the
statement applicable to arbitrary odd-characteristic residue rings, without
requiring a field instance.
-/

open Equiv Fintype Finset
open scoped BigOperators

namespace SunCotangent

section

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The sign attached to a row: rows in `negative` have sign `-1`, and all
other rows have sign `+1`. -/
private def glynnSign (negative : Finset n) (i : n) : R :=
  if i ∈ negative then -1 else 1

/-- The unnormalized numerator in Glynn's formula.  The distinguished row
`pivot` is excluded from `negative`, so its sign is fixed to `+1`. -/
def glynnSum (pivot : n) (M : Matrix n n R) : R :=
  ∑ negative ∈ (Finset.univ.erase pivot).powerset,
    (-1 : R) ^ negative.card *
      ∏ j : n, ∑ i : n, glynnSign negative i * M i j

/-- Glynn's normalized evaluator, parameterized by an explicit inverse of
`2`.  The theorem `glynnPermanent_eq_permanent` records the sole required
assumption on `twoInv`. -/
def glynnPermanent (twoInv : R) (pivot : n) (M : Matrix n n R) : R :=
  twoInv ^ (Fintype.card n - 1) * glynnSum pivot M

/-- Number of occurrences of row `i` in a function selecting one row for
each column. -/
private def fiberCard (f : n → n) (i : n) : ℕ :=
  #{j ∈ (Finset.univ : Finset n) | f j = i}

/-- After expansion of the column products, this is the coefficient of the
monomial indexed by `f`. -/
private def glynnCoefficient (pivot : n) (f : n → n) : R :=
  ∑ negative ∈ (Finset.univ.erase pivot).powerset,
    (-1 : R) ^ negative.card *
      ∏ j : n, glynnSign negative (f j)

/-- Group the signs in a monomial by fibers of `f`. -/
private theorem sign_product_eq_fiber_product (f : n → n) (negative : Finset n) :
    (-1 : R) ^ negative.card *
        ∏ j : n, glynnSign negative (f j) =
      ∏ i ∈ negative, (-1 : R) ^ (fiberCard f i + 1) := by
  classical
  have hfiber :
      (∑ i ∈ negative, fiberCard f i) =
        #{j ∈ (Finset.univ : Finset n) | f j ∈ negative} := by
    simpa only [fiberCard] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset n) negative f)
  have hsign :
      (∏ j : n, glynnSign negative (f j)) =
        (-1 : R) ^ #{j ∈ (Finset.univ : Finset n) | f j ∈ negative} := by
    change
      (∏ j ∈ (Finset.univ : Finset n),
          if f j ∈ negative then (-1 : R) else 1) = _
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
  calc
    (-1 : R) ^ negative.card * ∏ j : n, glynnSign negative (f j) =
        (-1 : R) ^
          (negative.card +
            #{j ∈ (Finset.univ : Finset n) | f j ∈ negative}) := by
      rw [hsign, pow_add]
    _ = (-1 : R) ^ (∑ i ∈ negative, (fiberCard f i + 1)) := by
      congr 1
      rw [Finset.sum_add_distrib, hfiber]
      simp [Nat.add_comm]
    _ = ∏ i ∈ negative, (-1 : R) ^ (fiberCard f i + 1) := by
      rw [Finset.prod_pow_eq_pow_sum]

/-- Character orthogonality turns the sign sum into a product of one-row
factors. -/
private theorem glynnCoefficient_eq_product (pivot : n) (f : n → n) :
    glynnCoefficient (R := R) pivot f =
      ∏ i ∈ Finset.univ.erase pivot,
        (1 + (-1 : R) ^ (fiberCard f i + 1)) := by
  classical
  unfold glynnCoefficient
  calc
    (∑ negative ∈ (Finset.univ.erase pivot).powerset,
        (-1 : R) ^ negative.card *
          ∏ j : n, glynnSign negative (f j)) =
        ∑ negative ∈ (Finset.univ.erase pivot).powerset,
          ∏ i ∈ negative, (-1 : R) ^ (fiberCard f i + 1) := by
      apply Finset.sum_congr rfl
      intro negative hnegative
      exact sign_product_eq_fiber_product f negative
    _ = ∏ i ∈ Finset.univ.erase pivot,
          (1 + (-1 : R) ^ (fiberCard f i + 1)) := by
      rw [Finset.prod_one_add]

/-- A bijection has singleton fibers. -/
private theorem fiberCard_eq_one_of_bijective (f : n → n)
    (hf : Function.Bijective f) (i : n) :
    fiberCard f i = 1 := by
  classical
  obtain ⟨x, hx⟩ := hf.2 i
  have hfilter :
      {j ∈ (Finset.univ : Finset n) | f j = i} = {x} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hj
      exact hf.1 (hj.trans hx.symm)
    · rintro rfl
      exact hx
  simp only [fiberCard, hfilter, Finset.card_singleton]

/-- If every fiber away from `pivot` is odd, then the pivot fiber is odd as
well.  The reason is that the sum of all fiber cardinalities is `card n`,
whereas there are exactly `card n - 1` off-pivot fibers. -/
private theorem odd_pivot_fiber_of_odd_off_pivot (pivot : n) (f : n → n)
    (hoff : ∀ i ∈ Finset.univ.erase pivot, Odd (fiberCard f i)) :
    Odd (fiberCard f pivot) := by
  classical
  let off : Finset n := Finset.univ.erase pivot
  have hfilter :
      {i ∈ off | Odd (fiberCard f i)} = off := by
    apply Finset.filter_eq_self.2
    intro i hi
    exact hoff i hi
  have hevenOff :
      Even (∑ i ∈ off, fiberCard f i) ↔ Even off.card := by
    rw [Finset.even_sum_iff_even_card_odd, hfilter]
  have htotalAll :
      Fintype.card n = ∑ i : n, fiberCard f i := by
    simpa only [Finset.card_univ, fiberCard] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset n))
        (t := (Finset.univ : Finset n))
        (f := f) (by intro i hi; simp))
  have htotal :
      Fintype.card n =
        fiberCard f pivot + ∑ i ∈ off, fiberCard f i := by
    calc
      Fintype.card n = ∑ i : n, fiberCard f i := htotalAll
      _ = fiberCard f pivot + ∑ i ∈ off, fiberCard f i := by
        simpa only [off] using
          (Finset.add_sum_erase (Finset.univ : Finset n) (fiberCard f)
            (Finset.mem_univ pivot)).symm
  have hnpos : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨pivot⟩
  have hcardOff : off.card + 1 = Fintype.card n := by
    dsimp only [off]
    rw [Finset.card_erase_of_mem (Finset.mem_univ pivot)]
    rw [Finset.card_univ]
    omega
  by_contra hpivot
  have hevenPivot : Even (fiberCard f pivot) :=
    Nat.not_odd_iff_even.mp hpivot
  have hevenTotal :
      Even (Fintype.card n) ↔
        Even (∑ i ∈ off, fiberCard f i) := by
    rw [htotal, Nat.even_add]
    simp only [hevenPivot, true_iff]
  have hflip : Even (Fintype.card n) ↔ ¬ Even off.card := by
    rw [← hcardOff, Nat.even_add_one]
  by_cases hparity : Even off.card
  · have : Even (Fintype.card n) :=
      hevenTotal.mpr (hevenOff.mpr hparity)
    exact (hflip.mp this) hparity
  · have : Even (Fintype.card n) := hflip.mpr hparity
    exact hparity (hevenOff.mp (hevenTotal.mp this))

/-- A non-bijective self-map has an even fiber away from the fixed pivot.
This is the precise cancellation input for Glynn's half-sign-vector sum. -/
private theorem exists_even_fiber_off_pivot_of_not_bijective
    (pivot : n) (f : n → n) (hf : ¬ Function.Bijective f) :
    ∃ i, i ≠ pivot ∧ Even (fiberCard f i) := by
  classical
  by_contra hno
  have hoff : ∀ i ∈ Finset.univ.erase pivot, Odd (fiberCard f i) := by
    intro i hi
    apply Nat.not_even_iff_odd.mp
    intro heven
    exact hno ⟨i, (Finset.mem_erase.mp hi).1, heven⟩
  have hpivot : Odd (fiberCard f pivot) :=
    odd_pivot_fiber_of_odd_off_pivot pivot f hoff
  have hall : ∀ i : n, Odd (fiberCard f i) := by
    intro i
    by_cases hi : i = pivot
    · simpa only [hi] using hpivot
    · exact hoff i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  have hsurj : Function.Surjective f := by
    intro i
    have hne : fiberCard f i ≠ 0 := by
      intro hzero
      have : Odd 0 := hzero ▸ hall i
      exact Nat.not_odd_zero this
    change #{j ∈ (Finset.univ : Finset n) | f j = i} ≠ 0 at hne
    obtain ⟨j, hj⟩ := Finset.card_ne_zero.mp hne
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  exact hf (Finite.surjective_iff_bijective.mp hsurj)

/-- Orthogonality of the fixed-pivot sign vectors: bijective selectors have
coefficient `2^(card n - 1)`, and every non-bijection cancels. -/
private theorem glynnCoefficient_eq_ite_bijective (pivot : n) (f : n → n) :
    glynnCoefficient (R := R) pivot f =
      if Function.Bijective f then
        (2 : R) ^ (Fintype.card n - 1)
      else 0 := by
  classical
  by_cases hf : Function.Bijective f
  · rw [if_pos hf, glynnCoefficient_eq_product]
    have hone : ∀ i : n, fiberCard f i = 1 :=
      fiberCard_eq_one_of_bijective f hf
    have hneg : (-1 : R) ^ (2 : ℕ) = 1 :=
      (even_two : Even (2 : ℕ)).neg_one_pow
    simp only [hone, one_add_one_eq_two, hneg, Finset.prod_const]
    rw [Finset.card_erase_of_mem (Finset.mem_univ pivot)]
    simp only [Finset.card_univ]
  · rw [if_neg hf, glynnCoefficient_eq_product]
    obtain ⟨i, hipivot, heven⟩ :=
      exists_even_fiber_off_pivot_of_not_bijective pivot f hf
    refine Finset.prod_eq_zero (i := i)
      (Finset.mem_erase.mpr ⟨hipivot, Finset.mem_univ i⟩) ?_
    rw [(heven.add_one).neg_one_pow]
    exact add_neg_cancel 1

/-- Expand a product of signed column sums into its function-indexed
monomials. -/
private theorem expand_signed_column_product (negative : Finset n)
    (M : Matrix n n R) :
    (∏ j : n, ∑ i : n, glynnSign negative i * M i j) =
      ∑ f : n → n,
        (∏ j : n, glynnSign negative (f j)) *
          ∏ j : n, M (f j) j := by
  classical
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.prod_mul_distrib]

/-- Summing the monomials indexed by bijective self-maps is exactly
Mathlib's definition of the permanent. -/
private theorem sum_bijective_functions_eq_permanent (M : Matrix n n R) :
    (∑ f : n → n with Function.Bijective f,
      ∏ j : n, M (f j) j) = M.permanent := by
  classical
  rw [Matrix.permanent]
  symm
  refine Finset.sum_bij (fun σ _ ↦ (σ : n → n)) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact σ.bijective
  · intro σ hσ τ hτ h
    exact Equiv.ext fun x ↦ congrFun h x
  · intro f hf
    have hbij : Function.Bijective f := (Finset.mem_filter.mp hf).2
    refine ⟨Equiv.ofBijective f hbij, Finset.mem_univ _, ?_⟩
    rfl
  · intro σ hσ
    rfl

/-- **Unnormalized Glynn formula.**  This identity requires no assumption
that `2` be invertible. -/
theorem glynnSum_eq_pow_mul_permanent (pivot : n) (M : Matrix n n R) :
    glynnSum pivot M =
      (2 : R) ^ (Fintype.card n - 1) * M.permanent := by
  classical
  calc
    glynnSum pivot M =
        ∑ negative ∈ (Finset.univ.erase pivot).powerset,
          ∑ f : n → n,
            (((-1 : R) ^ negative.card *
                ∏ j : n, glynnSign negative (f j)) *
              ∏ j : n, M (f j) j) := by
      unfold glynnSum
      apply Finset.sum_congr rfl
      intro negative hnegative
      rw [expand_signed_column_product, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      ring
    _ = ∑ f : n → n,
          glynnCoefficient (R := R) pivot f *
            ∏ j : n, M (f j) j := by
      unfold glynnCoefficient
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.sum_mul]
    _ = ∑ f : n → n with Function.Bijective f,
          (2 : R) ^ (Fintype.card n - 1) *
            ∏ j : n, M (f j) j := by
      simp only [glynnCoefficient_eq_ite_bijective, ite_mul, zero_mul,
        Finset.sum_ite, Finset.sum_const_zero, add_zero]
    _ = (2 : R) ^ (Fintype.card n - 1) *
          ∑ f : n → n with Function.Bijective f,
            ∏ j : n, M (f j) j := by
      rw [Finset.mul_sum]
    _ = (2 : R) ^ (Fintype.card n - 1) * M.permanent := by
      rw [sum_bijective_functions_eq_permanent]

/-- **Certified Glynn formula.**  If `twoInv * 2 = 1`, the normalized
fixed-pivot sign-vector sum agrees with `Matrix.permanent`. -/
theorem glynnPermanent_eq_permanent (twoInv : R)
    (htwo : twoInv * (2 : R) = 1) (pivot : n) (M : Matrix n n R) :
    glynnPermanent twoInv pivot M = M.permanent := by
  rw [glynnPermanent, glynnSum_eq_pow_mul_permanent]
  rw [← mul_assoc, ← mul_pow, htwo, one_pow, one_mul]

end

end SunCotangent
