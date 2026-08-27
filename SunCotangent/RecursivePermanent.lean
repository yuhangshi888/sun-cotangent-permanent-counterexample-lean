import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.Ring
import SunCotangent.PermanentDP

/-!
# A constant-space recursive Ryser evaluator

This module gives an evaluator independent of Gray-code adjacency.  It walks
the fourteen rows by a depth-first binary recursion.  The exclusion branch
keeps the vector of omitted column sums and its sign; the inclusion branch
adds the current row to all fourteen omitted sums and negates the sign.  At a
leaf it contributes the corresponding Ryser product.

Only the recursion stack and one fourteen-component state occur along any
branch.  The correctness proof is ring-generic and does not execute a concrete
permanent.
-/

open scoped BigOperators

namespace SunCotangent
namespace RecursivePermanent

abbrev Row := Fin 14
abbrev ColumnValues (R : Type*) := Fin 14 → R

/-- The sum of every row in each column, shared by all leaves. -/
def columnTotals {R : Type*} [AddCommMonoid R]
    (M : Matrix Row Row R) : ColumnValues R :=
  fun j ↦ ∑ i : Row, M i j

/-- Add one row to the vector of omitted column sums. -/
def includeRow {R : Type*} [Add R]
    (M : Matrix Row Row R) (i : Row) (omitted : ColumnValues R) :
    ColumnValues R :=
  fun j ↦ omitted j + M i j

/-- Constant-space binary traversal of the remaining row list. -/
def dfs {R : Type*} [CommRing R]
    (M : Matrix Row Row R) (totals : ColumnValues R) :
    List Row → ColumnValues R → R → R
  | [], omitted, sign =>
      sign * ∏ j : Row, (totals j - omitted j)
  | i :: rows, omitted, sign =>
      dfs M totals rows omitted sign +
        dfs M totals rows (includeRow M i omitted) (-sign)

/-- The recursive evaluator starts with no omitted rows and positive sign. -/
def recursivePermanent {R : Type*} [CommRing R]
    (M : Matrix Row Row R) : R :=
  let totals := columnTotals M
  dfs M totals (List.finRange 14) 0 1

/-! ## Declarative subset semantics -/

def ryserTerm {R : Type*} [CommRing R]
    (M : Matrix Row Row R) (omitted : Finset Row) : R :=
  (-1 : R) ^ omitted.card *
    ∏ j : Row, ∑ i ∈ (Finset.univ \ omitted), M i j

/-- The same binary recursion, retaining the chosen subset rather than its
incremental numerical state. -/
def subsetDFS {R : Type*} [CommRing R]
    (M : Matrix Row Row R) : List Row → Finset Row → R
  | [], omitted => ryserTerm M omitted
  | i :: rows, omitted =>
      subsetDFS M rows omitted + subsetDFS M rows (insert i omitted)

private theorem disjoint_tail {i : Row} {rows : List Row}
    {chosen : Finset Row}
    (hdisjoint : Disjoint (i :: rows).toFinset chosen) :
    Disjoint rows.toFinset chosen := by
  exact hdisjoint.mono (by simp) le_rfl

private theorem head_not_mem_chosen {i : Row} {rows : List Row}
    {chosen : Finset Row}
    (hdisjoint : Disjoint (i :: rows).toFinset chosen) :
    i ∉ chosen := by
  intro hi
  exact Finset.disjoint_left.mp hdisjoint (by simp) hi

private theorem disjoint_tail_insert {i : Row} {rows : List Row}
    {chosen : Finset Row}
    (hirows : i ∉ rows.toFinset)
    (hdisjoint : Disjoint (i :: rows).toFinset chosen) :
    Disjoint rows.toFinset (insert i chosen) := by
  rw [Finset.disjoint_left]
  intro x hx hxi
  rw [Finset.mem_insert] at hxi
  rcases hxi with rfl | hchosen
  · exact hirows hx
  · exact Finset.disjoint_left.mp (disjoint_tail hdisjoint) hx hchosen

/-- The numerical DFS state agrees with the chosen-subset recursion whenever
the cached sums and sign have their advertised meanings. -/
private theorem dfs_eq_subsetDFS {R : Type*} [CommRing R]
    (M : Matrix Row Row R) (totals : ColumnValues R)
    (htotals : totals = columnTotals M)
    (rows : List Row) (hrows : rows.Nodup)
    (chosen : Finset Row) (hdisjoint : Disjoint rows.toFinset chosen)
    (omitted : ColumnValues R)
    (homitted : ∀ j, omitted j = ∑ i ∈ chosen, M i j)
    (sign : R) (hsign : sign = (-1 : R) ^ chosen.card) :
    dfs M totals rows omitted sign = subsetDFS M rows chosen := by
  induction rows generalizing chosen omitted sign with
  | nil =>
      simp only [dfs, subsetDFS]
      rw [hsign]
      congr 1
      apply Finset.prod_congr rfl
      intro j _hj
      rw [htotals, homitted j]
      change (∑ i : Row, M i j) - ∑ i ∈ chosen, M i j =
        ∑ i ∈ (Finset.univ \ chosen), M i j
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ chosen)]
  | cons i rows ih =>
      have hirows : i ∉ rows.toFinset := by
        simpa using (List.nodup_cons.mp hrows).1
      have hrows' : rows.Nodup := (List.nodup_cons.mp hrows).2
      have hichosen : i ∉ chosen := head_not_mem_chosen hdisjoint
      have htail : Disjoint rows.toFinset chosen := disjoint_tail hdisjoint
      have hinsert : Disjoint rows.toFinset (insert i chosen) :=
        disjoint_tail_insert hirows hdisjoint
      have homittedInsert : ∀ j,
          includeRow M i omitted j = ∑ x ∈ insert i chosen, M x j := by
        intro j
        rw [Finset.sum_insert hichosen]
        simp only [includeRow, homitted j]
        ring
      have hsignInsert : -sign = (-1 : R) ^ (insert i chosen).card := by
        rw [Finset.card_insert_of_notMem hichosen, pow_succ, hsign]
        ring
      simp only [dfs, subsetDFS]
      rw [ih hrows' chosen htail omitted homitted sign hsign]
      rw [ih hrows' (insert i chosen) hinsert (includeRow M i omitted)
        homittedInsert (-sign) hsignInsert]

/-- The subset recursion enumerates every extension of `chosen` by a subset
of the remaining pairwise-distinct rows. -/
private theorem subsetDFS_eq_sum_powerset {R : Type*} [CommRing R]
    (M : Matrix Row Row R)
    (rows : List Row) (hrows : rows.Nodup)
    (chosen : Finset Row) (hdisjoint : Disjoint rows.toFinset chosen) :
    subsetDFS M rows chosen =
      ∑ s ∈ rows.toFinset.powerset, ryserTerm M (chosen ∪ s) := by
  induction rows generalizing chosen with
  | nil => simp [subsetDFS]
  | cons i rows ih =>
      have hirows : i ∉ rows.toFinset := by
        simpa using (List.nodup_cons.mp hrows).1
      have hrows' : rows.Nodup := (List.nodup_cons.mp hrows).2
      have htail : Disjoint rows.toFinset chosen := disjoint_tail hdisjoint
      have hinsert : Disjoint rows.toFinset (insert i chosen) :=
        disjoint_tail_insert hirows hdisjoint
      rw [subsetDFS, ih hrows' chosen htail,
        ih hrows' (insert i chosen) hinsert]
      rw [List.toFinset_cons, Finset.sum_powerset_insert hirows]
      congr 1
      apply Finset.sum_congr rfl
      intro s _hs
      apply congrArg (ryserTerm M)
      ext x
      simp

private theorem subsetDFS_all_eq_ryser {R : Type*} [CommRing R]
    (M : Matrix Row Row R) :
    subsetDFS M (List.finRange 14) ∅ = ryserPermanent M := by
  rw [subsetDFS_eq_sum_powerset M (List.finRange 14)
    (List.nodup_finRange 14) ∅ (by simp)]
  simp [ryserTerm, ryserPermanent]

/-- **Certified constant-space recursive permanent evaluator.** -/
theorem recursivePermanent_eq_permanent {R : Type*} [CommRing R]
    (M : Matrix Row Row R) :
    recursivePermanent M = Matrix.permanent M := by
  rw [recursivePermanent]
  have hstate :
      dfs M (columnTotals M) (List.finRange 14) 0 1 =
        subsetDFS M (List.finRange 14) ∅ := by
    apply dfs_eq_subsetDFS M (columnTotals M) rfl
      (List.finRange 14) (List.nodup_finRange 14) ∅ (by simp)
    · intro j
      simp
    · simp
  rw [hstate, subsetDFS_all_eq_ryser,
    SunCotangent.ryserPermanent_eq_permanent]

end RecursivePermanent
end SunCotangent
