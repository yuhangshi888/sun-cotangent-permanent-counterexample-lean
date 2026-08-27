import Init.Data.Array.Lemmas
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import SunCotangent.KernelPermanentDP

/-!
# A constant-space Gray-code permanent evaluator in dimension fourteen

The increasing-mask evaluator in `KernelPermanentDP` shares row sums by
retaining one fourteen-entry array for every mask.  This module instead visits
the same masks in reflected binary Gray-code order.  Consecutive masks differ
in one row, so a single fourteen-entry row-sum array can be updated in place
(functionally, as the next state) and no table of all masks is retained.

The Gray map is proved to be a permutation symbolically: on `BitVec 14`, xor
of the shifts of `x xor (x >> 1)` telescopes to `x`.  Each transition scans the
fourteen rows and reconciles their old/new mask memberships; this is proved
symbolically for arbitrary masks, so no large finite transition certificate is
needed.  The ring-valued computation and its identification with Ryser's
formula are proved symbolically for every commutative ring.
-/

open scoped BigOperators

namespace SunCotangent
namespace GrayPermanentDP

private abbrev GraySize : ℕ := 2 ^ 14

/-- Reflected-binary Gray transform at an arbitrary fixed width. -/
def grayBits {w : ℕ} (x : BitVec w) : BitVec w :=
  x ^^^ (x >>> 1)

/-- Xor the first `n` unsigned right shifts of `g`. -/
def ungrayAux {w : ℕ} (g : BitVec w) : ℕ → BitVec w
  | 0 => 0
  | n + 1 => ungrayAux g n ^^^ (g >>> n)

/-- Inverse Gray transform at width `w`. -/
def inverseGrayBits {w : ℕ} (g : BitVec w) : BitVec w :=
  ungrayAux g w

/-- The xor-shift inverse telescopes symbolically. -/
private theorem ungrayAux_grayBits {w : ℕ} (x : BitVec w) (n : ℕ) :
    ungrayAux (grayBits x) n = x ^^^ (x >>> n) := by
  induction n with
  | zero => simp [ungrayAux]
  | succ n ih =>
      simp only [ungrayAux]
      rw [ih]
      simp only [grayBits, BitVec.ushiftRight_xor_distrib]
      rw [← BitVec.shiftRight_add x 1 n, Nat.add_comm 1 n]
      rw [BitVec.xor_assoc]
      rw [← BitVec.xor_assoc (x >>> n) (x >>> n) (x >>> (n + 1))]
      simp

private theorem inverseGrayBits_grayBits {w : ℕ} (x : BitVec w) :
    inverseGrayBits (grayBits x) = x := by
  rw [inverseGrayBits, ungrayAux_grayBits]
  rw [BitVec.ushiftRight_eq_zero (x := x) (n := w) (by omega)]
  simp

/-- The reflected-binary Gray value of a natural number, truncated to fourteen
bits. -/
def grayValue (n : ℕ) : ℕ :=
  (grayBits (BitVec.ofNat 14 n)).toNat

/-- The inverse Gray value, truncated to fourteen bits. -/
def inverseGrayValue (g : ℕ) : ℕ :=
  (inverseGrayBits (BitVec.ofNat 14 g)).toNat

/-- Gray-code permutation on the fourteen-bit words. -/
def grayIndex (n : Fin GraySize) : Fin GraySize :=
  (grayBits (BitVec.ofFin n)).toFin

/-- Explicit inverse of `grayIndex`. -/
def inverseGrayIndex (g : Fin GraySize) : Fin GraySize :=
  (inverseGrayBits (BitVec.ofFin g)).toFin

private theorem inverseGray_leftInverse :
    Function.LeftInverse inverseGrayIndex grayIndex := by
  intro n
  apply Fin.ext
  simp [inverseGrayIndex, grayIndex, inverseGrayBits_grayBits]

private theorem inverseGray_rightInverse :
    Function.RightInverse inverseGrayIndex grayIndex := by
  apply inverseGray_leftInverse.rightInverse_of_surjective
  exact Finite.surjective_of_injective inverseGray_leftInverse.injective

/-- The certified permutation used to reindex the final finite sum. -/
def grayEquiv : Fin GraySize ≃ Fin GraySize where
  toFun := grayIndex
  invFun := inverseGrayIndex
  left_inv := inverseGray_leftInverse
  right_inv := inverseGray_rightInverse

/-- The predecessor of a nonzero scan index.  The definition is total, though
the transition theorem below only uses it away from zero. -/
def previousIndex (next : Fin GraySize) : Fin GraySize :=
  ⟨next.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) next.isLt⟩

/-- Declarative omitted-row sums for a Gray mask. -/
def subsetRowSums {R : Type*} [AddCommMonoid R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin GraySize) :
    KernelPermanentDP.RowValues R :=
  Array.ofFn fun j : Fin 14 =>
    ∑ i ∈ CyclotomicBitmask.maskSubset mask, M i j

/-- The scalar correction contributed by one row when changing masks. -/
def rowDelta {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (oldMask newMask : Fin GraySize) (row column : Fin 14) : R :=
  if oldMask.val.testBit row.val = newMask.val.testBit row.val then
    0
  else if newMask.val.testBit row.val then
    M row column
  else
    -M row column

/-- Bring one row's membership into agreement with the new mask.  Unchanged
rows return the same array without performing a ring operation. -/
def adjustRow {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (oldMask newMask : Fin GraySize)
    (sums : KernelPermanentDP.RowValues R) (row : Fin 14) :
    KernelPermanentDP.RowValues R :=
  if oldMask.val.testBit row.val = newMask.val.testBit row.val then
    sums
  else if newMask.val.testBit row.val then
    Array.ofFn fun j : Fin 14 => sums.getD j.val 0 + M row j
  else
    Array.ofFn fun j : Fin 14 => sums.getD j.val 0 - M row j

/-- Update one cached vector by scanning the fourteen candidate rows.  A Gray
transition executes the array update in exactly one of the fourteen branches,
while the symbolic proof below is valid for arbitrary old and new masks. -/
def updateRowSums {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (old : KernelPermanentDP.RowValues R) (next : Fin GraySize) :
    KernelPermanentDP.RowValues R :=
  let oldMask := grayIndex (previousIndex next)
  let newMask := grayIndex next
  (List.finRange 14).foldl (adjustRow M oldMask newMask) old

/-- One Ryser summand evaluated from the cached omitted-row sums. -/
def cachedTerm {R : Type*} [CommRing R]
    (totals omitted : KernelPermanentDP.RowValues R)
    (mask : Fin GraySize) : R :=
  (-1 : R) ^ (CyclotomicBitmask.maskSubset mask).card *
    ∏ j : Fin 14,
      (totals.getD (j : ℕ) 0 - omitted.getD (j : ℕ) 0)

/-- Constant-space scan state. -/
structure State (R : Type*) where
  rowSums : KernelPermanentDP.RowValues R
  totals : KernelPermanentDP.RowValues R
  accumulator : R

/-- Natural scan indices are reduced only to make the executable definition
total; all indices used by `permanentGray` are already below `2^14`. -/
def naturalIndex (n : ℕ) : Fin GraySize :=
  Fin.ofNat GraySize n

/-- The Gray mask at a natural scan index. -/
def grayAt (n : ℕ) : Fin GraySize :=
  grayIndex (naturalIndex n)

/-- Initial state, including the Ryser term for mask zero. -/
def initialState {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) : State R :=
  let totals := KernelPermanentDP.columnTotals M
  let omitted := KernelPermanentDP.zeroRow
  { rowSums := omitted
    totals := totals
    accumulator := cachedTerm totals omitted (grayAt 0) }

/-- Advance from Gray index `next - 1` to `next`. -/
def advance {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (state : State R)
    (next : Fin GraySize) : State R :=
  let omitted := updateRowSums M state.rowSums next
  { rowSums := omitted
    totals := state.totals
    accumulator := state.accumulator +
      cachedTerm state.totals omitted (grayIndex next) }

/-- Apply the transition ending at `k + 1`. -/
def step {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (state : State R) (k : ℕ) :
    State R :=
  advance M state (naturalIndex (k + 1))

/-- State after `stop` transitions, hence after Gray indices `0,...,stop`. -/
def run {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (stop : ℕ) : State R :=
  (List.range stop).foldl (step M) (initialState M)

/-- The constant-space evaluator visits all `2^14` masks. -/
def permanentGray {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) : R :=
  (run M (GraySize - 1)).accumulator

private theorem subsetRowSums_size {R : Type*} [AddCommMonoid R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin GraySize) :
    (subsetRowSums M mask).size = 14 := by
  simp [subsetRowSums]

private theorem subsetRowSums_getD_eq_sum {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin GraySize) (j : Fin 14) :
    (subsetRowSums M mask).getD j.val 0 =
      ∑ i ∈ CyclotomicBitmask.maskSubset mask, M i j := by
  have hj : j.val < (subsetRowSums M mask).size := by
    simp [subsetRowSums]
  rw [← Array.getElem_eq_getD
    (xs := subsetRowSums M mask) (i := j.val) (h := hj) 0]
  simp [subsetRowSums]

private theorem adjustRow_size {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (oldMask newMask : Fin GraySize)
    (sums : KernelPermanentDP.RowValues R) (row : Fin 14)
    (hsums : sums.size = 14) :
    (adjustRow M oldMask newMask sums row).size = 14 := by
  cases hold : oldMask.val.testBit row.val <;>
    cases hnew : newMask.val.testBit row.val <;>
      simp [adjustRow, hold, hnew, hsums]

private theorem adjustRow_getD {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (oldMask newMask : Fin GraySize)
    (sums : KernelPermanentDP.RowValues R) (row j : Fin 14) :
    (adjustRow M oldMask newMask sums row).getD j.val 0 =
      sums.getD j.val 0 + rowDelta M oldMask newMask row j := by
  cases hold : oldMask.val.testBit row.val <;>
    cases hnew : newMask.val.testBit row.val <;>
      simp [adjustRow, rowDelta, hold, hnew, sub_eq_add_neg]

private theorem foldAdjust_size {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (oldMask newMask : Fin GraySize) (rows : List (Fin 14))
    (sums : KernelPermanentDP.RowValues R) (hsums : sums.size = 14) :
    (rows.foldl (adjustRow M oldMask newMask) sums).size = 14 := by
  induction rows generalizing sums with
  | nil => exact hsums
  | cons row rows ih =>
      simp only [List.foldl_cons]
      exact ih _ (adjustRow_size M oldMask newMask sums row hsums)

private theorem foldAdjust_getD {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (oldMask newMask : Fin GraySize) (rows : List (Fin 14))
    (sums : KernelPermanentDP.RowValues R) (j : Fin 14) :
    (rows.foldl (adjustRow M oldMask newMask) sums).getD j.val 0 =
      sums.getD j.val 0 +
        (rows.map fun row => rowDelta M oldMask newMask row j).sum := by
  induction rows generalizing sums with
  | nil => simp
  | cons row rows ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, adjustRow_getD]
      ac_rfl

private theorem subsetSum_add_rowDeltas {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (oldMask newMask : Fin GraySize) (j : Fin 14) :
    (∑ i ∈ CyclotomicBitmask.maskSubset oldMask, M i j) +
        ∑ row : Fin 14, rowDelta M oldMask newMask row j =
      ∑ i ∈ CyclotomicBitmask.maskSubset newMask, M i j := by
  simp only [CyclotomicBitmask.maskSubset, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hold : oldMask.val.testBit row.val <;>
    by_cases hnew : newMask.val.testBit row.val <;>
      simp [rowDelta, hold, hnew]

theorem updateRowSums_eq_subsetRowSums {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (next : Fin GraySize) :
    updateRowSums M
        (subsetRowSums M (grayIndex (previousIndex next))) next =
      subsetRowSums M (grayIndex next) := by
  let oldMask := grayIndex (previousIndex next)
  let newMask := grayIndex next
  change (List.finRange 14).foldl (adjustRow M oldMask newMask)
      (subsetRowSums M oldMask) = subsetRowSums M newMask
  apply Array.ext
  · exact (foldAdjust_size M oldMask newMask _ _
      (subsetRowSums_size M oldMask)).trans
        (subsetRowSums_size M newMask).symm
  · intro k hk₁ hk₂
    have hk : k < 14 := by
      simpa only [subsetRowSums, Array.size_ofFn] using hk₂
    rw [Array.getElem_eq_getD
      (xs := (List.finRange 14).foldl (adjustRow M oldMask newMask)
        (subsetRowSums M oldMask)) (i := k) (h := hk₁) 0]
    rw [Array.getElem_eq_getD
      (xs := subsetRowSums M newMask) (i := k) (h := hk₂) 0]
    let j : Fin 14 := ⟨k, hk⟩
    change ((List.finRange 14).foldl (adjustRow M oldMask newMask)
        (subsetRowSums M oldMask)).getD j.val 0 =
      (subsetRowSums M newMask).getD j.val 0
    rw [foldAdjust_getD (M := M) (oldMask := oldMask)
      (newMask := newMask) (rows := List.finRange 14)
      (sums := subsetRowSums M oldMask) (j := j)]
    rw [subsetRowSums_getD_eq_sum, subsetRowSums_getD_eq_sum]
    rw [← List.sum_toFinset _ (List.nodup_finRange 14),
      List.toFinset_finRange]
    exact subsetSum_add_rowDeltas M oldMask newMask j

private theorem grayAt_zero : grayAt 0 = 0 := by
  decide +kernel

private theorem zeroRow_eq_subsetRowSums_gray_zero {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    (KernelPermanentDP.zeroRow : KernelPermanentDP.RowValues R) =
      subsetRowSums M (grayAt 0) := by
  rw [grayAt_zero]
  apply Array.ext
  · simp [KernelPermanentDP.zeroRow, subsetRowSums]
  · intro i hi₁ hi₂
    simp [KernelPermanentDP.zeroRow, subsetRowSums,
      CyclotomicBitmask.maskSubset]

private theorem naturalIndex_eq (n : ℕ) (hn : n < GraySize) :
    naturalIndex n = ⟨n, hn⟩ := by
  apply Fin.ext
  simp [naturalIndex, Nat.mod_eq_of_lt hn]

private theorem previous_naturalIndex_succ (n : ℕ)
    (hn : n + 1 < GraySize) :
    previousIndex (naturalIndex (n + 1)) = naturalIndex n := by
  apply Fin.ext
  simp only [previousIndex, naturalIndex, Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt (show n < GraySize by omega)]
  omega

private theorem run_succ {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) :
    run M (n + 1) = step M (run M n) n := by
  simp [run, List.range_succ, List.foldl_append]

private theorem run_totals {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) :
    (run M n).totals = KernelPermanentDP.columnTotals M := by
  induction n with
  | zero => simp [run, initialState]
  | succ n ih =>
      rw [run_succ]
      simp [step, advance, ih]

private theorem run_rowSums {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) (hn : n < GraySize) :
    (run M n).rowSums = subsetRowSums M (grayAt n) := by
  induction n with
  | zero =>
      change KernelPermanentDP.zeroRow = subsetRowSums M (grayAt 0)
      exact zeroRow_eq_subsetRowSums_gray_zero M
  | succ n ih =>
      have hn' : n < GraySize := by omega
      rw [run_succ]
      simp only [step, advance]
      rw [ih hn']
      have hupdate := updateRowSums_eq_subsetRowSums M
        (naturalIndex (n + 1))
      rw [previous_naturalIndex_succ n hn] at hupdate
      exact hupdate

private theorem run_accumulator {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (n : ℕ) (hn : n < GraySize) :
    (run M n).accumulator =
      ∑ k ∈ Finset.range (n + 1),
        cachedTerm (KernelPermanentDP.columnTotals M)
          (subsetRowSums M (grayAt k)) (grayAt k) := by
  induction n with
  | zero =>
      change cachedTerm (KernelPermanentDP.columnTotals M)
          KernelPermanentDP.zeroRow (grayAt 0) =
        ∑ k ∈ Finset.range 1,
          cachedTerm (KernelPermanentDP.columnTotals M)
            (subsetRowSums M (grayAt k)) (grayAt k)
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        zeroRow_eq_subsetRowSums_gray_zero M]
  | succ n ih =>
      have hn' : n < GraySize := by omega
      rw [run_succ]
      simp only [step, advance]
      rw [ih hn', run_totals, run_rowSums M n hn']
      have hupdate := updateRowSums_eq_subsetRowSums M
        (naturalIndex (n + 1))
      rw [previous_naturalIndex_succ n hn] at hupdate
      have hupdateGray :
          updateRowSums M (subsetRowSums M (grayAt n))
              (naturalIndex (n + 1)) =
            subsetRowSums M (grayAt (n + 1)) := by
        simpa only [grayAt] using hupdate
      rw [hupdateGray]
      simpa only [grayAt] using
        (Finset.sum_range_succ
          (fun k => cachedTerm (KernelPermanentDP.columnTotals M)
            (subsetRowSums M (grayAt k)) (grayAt k)) (n + 1)).symm

private theorem subsetRowSums_getD_eq_filterSum {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin GraySize) (j : Fin 14) :
    (subsetRowSums M mask).getD j.val 0 =
      ∑ i : Fin 14, if mask.val.testBit i.val then M i j else 0 := by
  have hj : j.val < (subsetRowSums M mask).size := by
    simp [subsetRowSums]
  rw [← Array.getElem_eq_getD
    (xs := subsetRowSums M mask) (i := j.val) (h := hj) 0]
  simp only [subsetRowSums, Array.getElem_ofFn]
  simp only [CyclotomicBitmask.maskSubset, Finset.sum_filter]

private theorem columnTotals_sub_subset_eq_allowedSum {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin GraySize) (j : Fin 14) :
    (KernelPermanentDP.columnTotals M).getD j.val 0 -
        (subsetRowSums M mask).getD j.val 0 =
      ∑ i : Fin 14, if mask.val.testBit i.val then 0 else M i j := by
  have hj : j.val < (KernelPermanentDP.columnTotals M).size := by
    simp [KernelPermanentDP.columnTotals]
  rw [← Array.getElem_eq_getD
    (xs := KernelPermanentDP.columnTotals M) (i := j.val) (h := hj) 0]
  simp only [KernelPermanentDP.columnTotals, Array.getElem_ofFn]
  rw [subsetRowSums_getD_eq_filterSum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hbit : mask.val.testBit i.val <;> simp [hbit]

private theorem cachedTerm_eq_bitmaskTerm {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (mask : Fin GraySize) :
    cachedTerm (KernelPermanentDP.columnTotals M) (subsetRowSums M mask) mask =
      (-1 : R) ^ (CyclotomicBitmask.maskSubset mask).card *
        ∏ j : Fin 14, ∑ i : Fin 14,
          if mask.val.testBit i.val then 0 else M i j := by
  unfold cachedTerm
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact columnTotals_sub_subset_eq_allowedSum M mask j

private theorem sum_grayAt_eq_sum_grayIndex {R : Type*} [AddCommMonoid R]
    (f : Fin GraySize → R) :
    (∑ k ∈ Finset.range GraySize, f (grayAt k)) =
      ∑ i : Fin GraySize, f (grayIndex i) := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < GraySize := Finset.mem_range.mp hk
  simp only [dif_pos hk']
  rw [grayAt, naturalIndex_eq k hk']

/-- The Gray scan is exactly the certified bitmask Ryser sum. -/
theorem permanentGray_eq_bitmaskRyser {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    permanentGray M = CyclotomicBitmask.bitmaskRyser M := by
  unfold permanentGray
  have hlast : GraySize - 1 < GraySize := by
    norm_num [GraySize]
  rw [run_accumulator M _ hlast]
  norm_num [GraySize]
  calc
    (∑ k ∈ Finset.range GraySize,
        cachedTerm (KernelPermanentDP.columnTotals M)
          (subsetRowSums M (grayAt k)) (grayAt k)) =
        ∑ i : Fin GraySize,
          cachedTerm (KernelPermanentDP.columnTotals M)
            (subsetRowSums M (grayIndex i)) (grayIndex i) :=
      sum_grayAt_eq_sum_grayIndex
        (f := fun mask => cachedTerm (KernelPermanentDP.columnTotals M)
          (subsetRowSums M mask) mask)
    _ = ∑ mask : Fin GraySize,
          cachedTerm (KernelPermanentDP.columnTotals M)
            (subsetRowSums M mask) mask :=
      grayEquiv.sum_comp
        (fun mask => cachedTerm (KernelPermanentDP.columnTotals M)
          (subsetRowSums M mask) mask)
    _ = CyclotomicBitmask.bitmaskRyser M := by
      unfold CyclotomicBitmask.bitmaskRyser
      apply Finset.sum_congr rfl
      intro mask _
      exact cachedTerm_eq_bitmaskTerm M mask

/-- **Certified constant-space permanent evaluator.** -/
theorem permanentGray_eq_permanent {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    permanentGray M = Matrix.permanent M := by
  rw [permanentGray_eq_bitmaskRyser,
    CyclotomicBitmask.bitmaskRyser_eq_permanent]

end GrayPermanentDP
end SunCotangent
