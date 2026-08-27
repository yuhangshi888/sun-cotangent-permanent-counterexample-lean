import Mathlib.Combinatorics.Colex
import Init.Data.Array.Lemmas
import Mathlib.Data.Finset.Fin
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import SunCotangent.CyclotomicBitmask

/-!
# A shared-array permanent evaluator for fourteen by fourteen matrices

The direct bitmask form of Ryser's formula recomputes fourteen row sums for
each of its fourteen columns at every mask.  Here those row sums are shared.
Masks are visited in increasing order.  For a nonzero mask, deleting its
least set bit gives a smaller mask whose row-sum vector has already been
stored, so the new vector costs only fourteen additions.

The accumulator is still exactly the proved bitmask Ryser sum.  Consequently
the executable evaluator below agrees with `Matrix.permanent` over every
commutative ring; arrays are only an implementation device.
-/

open scoped BigOperators

namespace SunCotangent
namespace KernelPermanentDP

/-- Fourteen ring values, represented by an array for constant-time lookup
during closed kernel evaluation. -/
abbrev RowValues (R : Type*) := Array R

/-- The zero vector used for the empty mask and as an unreachable fallback. -/
def zeroRow {R : Type*} [Zero R] : RowValues R :=
  Array.replicate 14 0

/-- The full sum of every matrix column, materialized once. -/
def columnTotals {R : Type*} [AddCommMonoid R]
    (M : Matrix (Fin 14) (Fin 14) R) : RowValues R :=
  Array.ofFn fun j : Fin 14 => ∑ i : Fin 14, M i j

/-- Declarative meaning of the cached vector for a natural-number mask.

`Fin.ofNat` is deliberate: this definition is total for every natural mask.
For the masks below `2^14`, every index in `bitIndices` is already below 14,
so no reduction modulo 14 occurs. -/
def subsetRowSums {R : Type*} [AddCommMonoid R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : ℕ) : RowValues R :=
  Array.ofFn fun j : Fin 14 =>
    (mask.bitIndices.map fun i => M (Fin.ofNat 14 i) j).sum

/-- The least set-bit position.  Its fallback is used only at mask zero. -/
def leastBit (mask : ℕ) : ℕ :=
  mask.bitIndices.headD 0

/-- Compute the next cached row-sum vector from a previously built table. -/
def nextRowSums {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (table : Array (RowValues R)) (mask : ℕ) : RowValues R :=
  if mask = 0 then
    zeroRow
  else
    let i := leastBit mask
    let previous := table.getD (mask - 2 ^ i) zeroRow
    Array.ofFn fun j : Fin 14 =>
      previous.getD j.val 0 + M (Fin.ofNat 14 i) j

/-- One Ryser summand, using cached omitted-row sums. -/
def cachedTerm {R : Type*} [CommRing R]
    (totals omitted : RowValues R) (mask : ℕ) : R :=
  (-1 : R) ^ mask.bitIndices.length *
    ∏ j : Fin 14, (totals.getD (j : ℕ) 0 - omitted.getD (j : ℕ) 0)

/-- State of the increasing-mask scan.  `totals` is carried in the state so
the closed evaluator shares its materialized array. -/
structure State (R : Type*) where
  table : Array (RowValues R)
  totals : RowValues R
  accumulator : R

/-- Initial state before any mask has been visited. -/
def initialState {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) : State R where
  table := #[]
  totals := columnTotals M
  accumulator := 0

/-- Append the vector for `mask` and add its Ryser summand. -/
def step {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (state : State R) (mask : ℕ) : State R :=
  let omitted := nextRowSums M state.table mask
  { table := state.table.push omitted
    totals := state.totals
    accumulator := state.accumulator + cachedTerm state.totals omitted mask }

/-- State after visiting masks `0, ..., stop - 1`. -/
def run {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (stop : ℕ) : State R :=
  (List.range stop).foldl (step M) (initialState M)

/-- The shared-array evaluator.  It visits exactly the `2^14` masks. -/
def permanentDP {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) : R :=
  (run M (2 ^ 14)).accumulator

private theorem bitIndices_ne_nil {mask : ℕ} (hmask : mask ≠ 0) :
    mask.bitIndices ≠ [] := by
  intro hnil
  have hsum := Nat.sum_map_two_pow_bitIndices mask
  rw [hnil] at hsum
  simp only [List.map_nil, List.sum_nil] at hsum
  exact hmask hsum.symm

private theorem leastBit_mem_bitIndices {mask : ℕ} (hmask : mask ≠ 0) :
    leastBit mask ∈ mask.bitIndices := by
  unfold leastBit
  cases hbits : mask.bitIndices with
  | nil => exact (bitIndices_ne_nil hmask hbits).elim
  | cons i tail => simp

/-- Clearing the least set bit removes precisely the head of `bitIndices`. -/
private theorem bitIndices_clear_least {mask : ℕ} (hmask : mask ≠ 0) :
    (mask - 2 ^ leastBit mask).bitIndices = mask.bitIndices.tail := by
  cases hbits : mask.bitIndices with
  | nil => exact (bitIndices_ne_nil hmask hbits).elim
  | cons i tail =>
      have hsorted : tail.SortedLT := by
        have hs := Nat.bitIndices_sorted (n := mask)
        rw [hbits] at hs
        exact hs.pairwise.tail.sortedLT
      have hsum := Nat.sum_map_two_pow_bitIndices mask
      rw [hbits] at hsum
      simp only [List.map_cons, List.sum_cons] at hsum
      have hsub : mask - 2 ^ i = (tail.map fun k => 2 ^ k).sum := by
        omega
      have hleast : leastBit mask = i := by
        unfold leastBit
        rw [hbits]
        rfl
      rw [hleast, hsub]
      exact Nat.bitIndices_sum_map_two_pow hsorted

private theorem clearLeast_lt {mask : ℕ} (hmask : mask ≠ 0) :
    mask - 2 ^ leastBit mask < mask := by
  exact Nat.sub_lt (Nat.pos_of_ne_zero hmask) (by positivity)

private theorem getD_push_lt {R : Type*} (table : Array R) (value fallback : R)
    {i : ℕ} (hi : i < table.size) :
    (table.push value).getD i fallback = table.getD i fallback := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  simp [Nat.ne_of_lt hi]

private theorem getD_push_eq {R : Type*} (table : Array R) (value fallback : R) :
    (table.push value).getD table.size fallback = value := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  simp

private theorem zeroRow_size {R : Type*} [Zero R] :
    (zeroRow : RowValues R).size = 14 := by
  simp [zeroRow]

private theorem subsetRowSums_size {R : Type*} [AddCommMonoid R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : ℕ) :
    (subsetRowSums M mask).size = 14 := by
  simp [subsetRowSums]

private theorem zeroRow_eq_subsetRowSums_zero {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    (zeroRow : RowValues R) = subsetRowSums M 0 := by
  apply Array.ext
  · simp [zeroRow, subsetRowSums]
  · intro i hi₁ hi₂
    simp [zeroRow, subsetRowSums]

private theorem subsetRowSums_clear_least {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) {mask : ℕ} (hmask : mask ≠ 0) :
    subsetRowSums M mask =
      Array.ofFn fun j : Fin 14 =>
        (subsetRowSums M (mask - 2 ^ leastBit mask)).getD j.val 0 +
          M (Fin.ofNat 14 (leastBit mask)) j := by
  cases hbits : mask.bitIndices with
  | nil => exact (bitIndices_ne_nil hmask hbits).elim
  | cons i tail =>
      have hleast : leastBit mask = i := by
        unfold leastBit
        rw [hbits]
        rfl
      have hclear := bitIndices_clear_least hmask
      rw [hbits] at hclear
      simp only [List.tail_cons] at hclear
      have hsum (j : Fin 14) :
          (mask.bitIndices.map fun k => M (Fin.ofNat 14 k) j).sum =
            ((mask - 2 ^ leastBit mask).bitIndices.map fun k =>
              M (Fin.ofNat 14 k) j).sum +
              M (Fin.ofNat 14 (leastBit mask)) j := by
        rw [hbits, hclear, hleast]
        simp only [List.map_cons, List.sum_cons]
        exact add_comm _ _
      apply Array.ext
      · simp [subsetRowSums]
      · intro j hj₁ hj₂
        have hj : j < 14 := by
          simpa only [subsetRowSums, Array.size_ofFn] using hj₁
        have hjprev :
            j < (subsetRowSums M (mask - 2 ^ leastBit mask)).size := by
          simpa [subsetRowSums] using hj₁
        simp only [Array.getElem_ofFn]
        rw [← Array.getElem_eq_getD
          (xs := subsetRowSums M (mask - 2 ^ leastBit mask))
          (i := j) (h := hjprev) 0]
        simp only [subsetRowSums, Array.getElem_ofFn]
        exact hsum ⟨j, hj⟩

private theorem nextRowSums_eq_subsetRowSums {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (table : Array (RowValues R)) (mask : ℕ)
    (htable : ∀ k < mask, table.getD k zeroRow = subsetRowSums M k) :
    nextRowSums M table mask = subsetRowSums M mask := by
  by_cases hmask : mask = 0
  · subst mask
    simp only [nextRowSums, if_pos]
    exact zeroRow_eq_subsetRowSums_zero M
  · simp only [nextRowSums, if_neg hmask]
    rw [htable _ (clearLeast_lt hmask)]
    exact (subsetRowSums_clear_least M hmask).symm

private theorem run_succ {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) :
    run M (n + 1) = step M (run M n) n := by
  simp [run, List.range_succ, List.foldl_append]

private theorem run_table_size {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) :
    (run M n).table.size = n := by
  induction n with
  | zero => simp [run, initialState]
  | succ n ih =>
      rw [run_succ]
      simp [step, ih]

private theorem run_totals {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) :
    (run M n).totals = columnTotals M := by
  induction n with
  | zero => simp [run, initialState]
  | succ n ih =>
      rw [run_succ]
      simp [step, ih]

private theorem run_table_getD {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) {n k : ℕ} (hk : k < n) :
    (run M n).table.getD k zeroRow = subsetRowSums M k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      rw [run_succ]
      simp only [step]
      by_cases hkn : k < n
      · rw [getD_push_lt]
        · exact ih hkn
        · simpa [run_table_size M n] using hkn
      · have hkeq : k = n := by omega
        subst k
        have hnext : nextRowSums M (run M n).table n = subsetRowSums M n := by
          apply nextRowSums_eq_subsetRowSums
          intro k hk
          exact ih hk
        calc
          ((run M n).table.push
              (nextRowSums M (run M n).table n)).getD n zeroRow =
              ((run M n).table.push
                (nextRowSums M (run M n).table n)).getD
                  (run M n).table.size zeroRow := by
            rw [run_table_size M n]
          _ = nextRowSums M (run M n).table n :=
            getD_push_eq _ _ _
          _ = subsetRowSums M n := hnext

private theorem run_accumulator {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) :
    (run M n).accumulator =
      ∑ mask ∈ Finset.range n,
        cachedTerm (columnTotals M) (subsetRowSums M mask) mask := by
  induction n with
  | zero => simp [run, initialState]
  | succ n ih =>
      rw [run_succ]
      simp only [step]
      rw [ih, run_totals]
      have hnext : nextRowSums M (run M n).table n = subsetRowSums M n := by
        apply nextRowSums_eq_subsetRowSums
        intro k hk
        exact run_table_getD M hk
      rw [hnext, Finset.sum_range_succ]

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
    CyclotomicBitmask.maskSubset mask =
      mask.val.bitIndices.toFinset.attachFin (bitIndices_bounded mask) := by
  ext i
  simp [CyclotomicBitmask.maskSubset, Nat.mem_bitIndices]

private theorem bitIndices_length_eq_maskSubset_card (mask : Fin (2 ^ 14)) :
    mask.val.bitIndices.length = (CyclotomicBitmask.maskSubset mask).card := by
  rw [maskSubset_eq_attachFin]
  simp [List.toFinset_card_of_nodup Nat.bitIndices_nodup]

private theorem sum_attachFin_val {R : Type*} [AddCommMonoid R]
    (s : Finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) (f : ℕ → R) :
    (∑ i ∈ s.attachFin h, f i.val) = ∑ m ∈ s, f m := by
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i hi
    exact (Finset.mem_attachFin h).mp hi
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro m hm
    let i : Fin n := ⟨m, h m hm⟩
    exact ⟨i, (Finset.mem_attachFin h).mpr hm, rfl⟩
  · intro i _
    rfl

private theorem subsetRowSums_getD_eq_filterSum {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin (2 ^ 14)) (j : Fin 14) :
    (subsetRowSums M mask.val).getD j.val 0 =
      ∑ i : Fin 14, if mask.val.testBit i.val then M i j else 0 := by
  have hj : j.val < (subsetRowSums M mask.val).size := by
    simp [subsetRowSums]
  rw [← Array.getElem_eq_getD
    (xs := subsetRowSums M mask.val) (i := j.val) (h := hj) 0]
  simp only [subsetRowSums, Array.getElem_ofFn]
  calc
    (mask.val.bitIndices.map fun i => M (Fin.ofNat 14 i) j).sum =
        ∑ i ∈ mask.val.bitIndices.toFinset, M (Fin.ofNat 14 i) j := by
      rw [List.sum_toFinset _ Nat.bitIndices_nodup]
    _ = ∑ i ∈ mask.val.bitIndices.toFinset.attachFin
          (bitIndices_bounded mask), M i j := by
      symm
      calc
        ∑ i ∈ mask.val.bitIndices.toFinset.attachFin
              (bitIndices_bounded mask), M i j =
            ∑ i ∈ mask.val.bitIndices.toFinset.attachFin
              (bitIndices_bounded mask), M (Fin.ofNat 14 i.val) j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Fin.ofNat_val_eq_self]
        _ = ∑ i ∈ mask.val.bitIndices.toFinset,
              M (Fin.ofNat 14 i) j :=
          sum_attachFin_val (R := R)
            (s := mask.val.bitIndices.toFinset) (n := 14)
            (h := bitIndices_bounded mask)
            (f := fun i => M (Fin.ofNat 14 i) j)
    _ = ∑ i ∈ CyclotomicBitmask.maskSubset mask, M i j := by
      rw [maskSubset_eq_attachFin]
    _ = ∑ i : Fin 14, if mask.val.testBit i.val then M i j else 0 := by
      rw [CyclotomicBitmask.maskSubset, Finset.sum_filter]

private theorem columnTotals_sub_subset_eq_allowedSum {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin (2 ^ 14)) (j : Fin 14) :
    (columnTotals M).getD j.val 0 -
        (subsetRowSums M mask.val).getD j.val 0 =
      ∑ i : Fin 14, if mask.val.testBit i.val then 0 else M i j := by
  have hj : j.val < (columnTotals M).size := by
    simp [columnTotals]
  rw [← Array.getElem_eq_getD
    (xs := columnTotals M) (i := j.val) (h := hj) 0]
  simp only [columnTotals, Array.getElem_ofFn]
  rw [subsetRowSums_getD_eq_filterSum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hbit : mask.val.testBit i.val <;> simp [hbit]

private theorem cachedTerm_eq_bitmaskTerm {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin (2 ^ 14)) :
    cachedTerm (columnTotals M) (subsetRowSums M mask.val) mask.val =
      (-1 : R) ^ (CyclotomicBitmask.maskSubset mask).card *
        ∏ j : Fin 14, ∑ i : Fin 14,
          if mask.val.testBit i.val then 0 else M i j := by
  unfold cachedTerm
  rw [bitIndices_length_eq_maskSubset_card]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact columnTotals_sub_subset_eq_allowedSum M mask j

/-- The shared-array scan is exactly the already certified bitmask Ryser sum. -/
theorem permanentDP_eq_bitmaskRyser {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    permanentDP M = CyclotomicBitmask.bitmaskRyser M := by
  unfold permanentDP
  rw [run_accumulator]
  unfold CyclotomicBitmask.bitmaskRyser
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro mask hmask
  have hm : mask < 2 ^ 14 := Finset.mem_range.mp hmask
  simp only [dif_pos hm]
  exact cachedTerm_eq_bitmaskTerm M ⟨mask, Finset.mem_range.mp hmask⟩

/-- **Certified shared-array permanent evaluator.** -/
theorem permanentDP_eq_permanent {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    permanentDP M = Matrix.permanent M := by
  rw [permanentDP_eq_bitmaskRyser,
    CyclotomicBitmask.bitmaskRyser_eq_permanent]

end KernelPermanentDP
end SunCotangent
