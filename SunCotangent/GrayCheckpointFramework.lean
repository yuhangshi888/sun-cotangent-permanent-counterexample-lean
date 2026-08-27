import SunCotangent.GrayPermanentDP

/-!
# A reusable 128-block certificate for the fourteen-dimensional Gray scan

The expensive modular certificates in this project all use the same scan
geometry.  This file separates that symbolic geometry from the concrete
checkpoint numbers.  A client supplies only the 129 accumulator values and
kernel proofs of the 128 local blocks.  Row sums and column totals are not
trusted checkpoint data: they are reconstructed from the matrix and
transported symbolically.
-/

namespace SunCotangent
namespace GrayCheckpointFramework

private abbrev GraySize : ℕ := 2 ^ 14

def checkpointPosition (i : Fin 129) : ℕ :=
  if i.val = 128 then 16383 else 128 * i.val

def currentIndex (i : Fin 128) : Fin 129 :=
  ⟨i.val, by omega⟩

def nextIndex (i : Fin 128) : Fin 129 :=
  ⟨i.val + 1, by omega⟩

def blockStart (i : Fin 128) : ℕ :=
  128 * i.val

def blockCount (i : Fin 128) : ℕ :=
  if i.val = 127 then 127 else 128

def blockStop (i : Fin 128) : ℕ :=
  blockStart i + blockCount i

theorem checkpointPosition_current (i : Fin 128) :
    checkpointPosition (currentIndex i) = blockStart i := by
  unfold checkpointPosition currentIndex blockStart
  rw [if_neg (Nat.ne_of_lt i.isLt)]

theorem checkpointPosition_next (i : Fin 128) :
    checkpointPosition (nextIndex i) = blockStop i := by
  unfold checkpointPosition nextIndex blockStop blockStart blockCount
  by_cases hlast : i.val = 127
  · simp [hlast]
  · have hnext : i.val + 1 ≠ 128 := by omega
    simp [hlast, hnext, Nat.mul_add]

theorem blockStop_lt (i : Fin 128) :
    blockStop i < GraySize := by
  unfold blockStop blockStart blockCount GraySize
  split <;> omega

abbrev ScanState (R : Type*) := GrayPermanentDP.State R

def checkpointState {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (stop : ℕ) (accumulator : R) : ScanState R where
  rowSums := GrayPermanentDP.subsetRowSums M
    (GrayPermanentDP.grayAt stop)
  totals := KernelPermanentDP.columnTotals M
  accumulator := accumulator

def resumeScan {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (start count : ℕ) (state : ScanState R) : ScanState R :=
  (List.range' start count).foldl (GrayPermanentDP.step M) state

theorem state_ext {R : Type*} {a b : ScanState R}
    (hrowSums : a.rowSums = b.rowSums)
    (htotals : a.totals = b.totals)
    (haccumulator : a.accumulator = b.accumulator) : a = b := by
  cases a
  cases b
  simp_all

private theorem previous_naturalIndex_succ (n : ℕ)
    (hn : n + 1 < GraySize) :
    GrayPermanentDP.previousIndex
        (GrayPermanentDP.naturalIndex (n + 1)) =
      GrayPermanentDP.naturalIndex n := by
  apply Fin.ext
  simp only [GrayPermanentDP.previousIndex,
    GrayPermanentDP.naturalIndex, Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt (show n < GraySize by omega)]
  omega

theorem resumeScan_succ {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (start count : ℕ) (state : ScanState R) :
    resumeScan M start (count + 1) state =
      resumeScan M (start + 1) count
        (GrayPermanentDP.step M state start) := by
  simp [resumeScan, List.range'_succ]

theorem resumeScan_rowSums {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (start count : ℕ) (state : ScanState R)
    (hrowSums : state.rowSums =
      GrayPermanentDP.subsetRowSums M (GrayPermanentDP.grayAt start))
    (hbound : start + count < GraySize) :
    (resumeScan M start count state).rowSums =
      GrayPermanentDP.subsetRowSums M
        (GrayPermanentDP.grayAt (start + count)) := by
  induction count generalizing start state with
  | zero =>
      simpa [resumeScan] using hrowSums
  | succ count ih =>
      rw [resumeScan_succ]
      have hstep :
          (GrayPermanentDP.step M state start).rowSums =
            GrayPermanentDP.subsetRowSums M
              (GrayPermanentDP.grayAt (start + 1)) := by
        simp only [GrayPermanentDP.step, GrayPermanentDP.advance]
        rw [hrowSums]
        have hupdate :=
          GrayPermanentDP.updateRowSums_eq_subsetRowSums M
            (GrayPermanentDP.naturalIndex (start + 1))
        rw [previous_naturalIndex_succ start (by omega)] at hupdate
        simpa only [GrayPermanentDP.grayAt] using hupdate
      have hrec := ih (start := start + 1)
        (state := GrayPermanentDP.step M state start) hstep (by omega)
      rw [show (start + 1) + count = start + (count + 1) by omega] at hrec
      exact hrec

theorem resumeScan_totals {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (start count : ℕ) (state : ScanState R)
    (htotals : state.totals = KernelPermanentDP.columnTotals M) :
    (resumeScan M start count state).totals =
      KernelPermanentDP.columnTotals M := by
  induction count generalizing start state with
  | zero =>
      simpa [resumeScan] using htotals
  | succ count ih =>
      rw [resumeScan_succ]
      apply ih
      simpa only [GrayPermanentDP.step, GrayPermanentDP.advance] using
        htotals

theorem resumeScan_checkpointState_eq {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (checkpoint : Fin 129 → R) (i : Fin 128)
    (haccumulator :
      (resumeScan M (blockStart i) (blockCount i)
        (checkpointState M (blockStart i)
          (checkpoint (currentIndex i)))).accumulator =
            checkpoint (nextIndex i)) :
    resumeScan M (blockStart i) (blockCount i)
        (checkpointState M (blockStart i)
          (checkpoint (currentIndex i))) =
      checkpointState M (blockStop i) (checkpoint (nextIndex i)) := by
  apply state_ext
  · exact resumeScan_rowSums M _ _ _ rfl (blockStop_lt i)
  · exact resumeScan_totals M _ _ _ rfl
  · exact haccumulator

theorem resumeScan_append {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (start first second : ℕ) (state : ScanState R) :
    resumeScan M start (first + second) state =
      resumeScan M (start + first) second
        (resumeScan M start first state) := by
  unfold resumeScan
  rw [← List.range'_append (s := start) (m := first)
    (n := second) (step := 1)]
  simp only [one_mul, List.foldl_append]

theorem run_eq_resumeScan {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) (stop : ℕ) :
    GrayPermanentDP.run M stop =
      resumeScan M 0 stop (GrayPermanentDP.initialState M) := by
  simp [GrayPermanentDP.run, resumeScan, List.range'_eq_map_range]

private theorem grayAt_zero : GrayPermanentDP.grayAt 0 = 0 := by
  decide +kernel

theorem initial_rowSums {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R) :
    (GrayPermanentDP.initialState M).rowSums =
      GrayPermanentDP.subsetRowSums M (GrayPermanentDP.grayAt 0) := by
  change (KernelPermanentDP.zeroRow : KernelPermanentDP.RowValues R) =
    GrayPermanentDP.subsetRowSums M (GrayPermanentDP.grayAt 0)
  rw [grayAt_zero]
  apply Array.ext
  · simp [KernelPermanentDP.zeroRow, GrayPermanentDP.subsetRowSums]
  · intro j hj₁ hj₂
    simp [KernelPermanentDP.zeroRow, GrayPermanentDP.subsetRowSums,
      CyclotomicBitmask.maskSubset]

abbrev CheckpointBlockStatement {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (checkpoint : Fin 129 → R) (i : Fin 128) : Prop :=
  (resumeScan M (blockStart i) (blockCount i)
    (checkpointState M (blockStart i)
      (checkpoint (currentIndex i)))).accumulator =
    checkpoint (nextIndex i)

def groupIndex (group : Fin 8) (offset : Fin 16) : Fin 128 :=
  ⟨16 * group.val + offset.val, by omega⟩

private theorem checkpointStateBlock {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (checkpoint : Fin 129 → R)
    (hblocks : ∀ i, CheckpointBlockStatement M checkpoint i)
    (i : Fin 128) :
    resumeScan M (blockStart i) (blockCount i)
        (checkpointState M (blockStart i)
          (checkpoint (currentIndex i))) =
      checkpointState M (blockStop i) (checkpoint (nextIndex i)) :=
  resumeScan_checkpointState_eq M checkpoint i (hblocks i)

private theorem checkpointChain {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (checkpoint : Fin 129 → R)
    (hblocks : ∀ i, CheckpointBlockStatement M checkpoint i)
    (k : ℕ) (hk : k ≤ 128) :
    resumeScan M 0 (checkpointPosition ⟨k, by omega⟩)
        (checkpointState M 0 (checkpoint 0)) =
      checkpointState M (checkpointPosition ⟨k, by omega⟩)
        (checkpoint ⟨k, by omega⟩) := by
  induction k with
  | zero =>
      simp [checkpointPosition, resumeScan]
  | succ k ih =>
      have hklt : k < 128 := by omega
      let i : Fin 128 := ⟨k, hklt⟩
      have hcurrent := ih (by omega)
      change resumeScan M 0 (checkpointPosition (nextIndex i))
          (checkpointState M 0 (checkpoint 0)) =
        checkpointState M (checkpointPosition (nextIndex i))
          (checkpoint (nextIndex i))
      rw [checkpointPosition_next i]
      have hindex : (⟨k, by omega⟩ : Fin 129) = currentIndex i := by
        apply Fin.ext
        rfl
      have hcurrent' :
          resumeScan M 0 (blockStart i)
              (checkpointState M 0 (checkpoint 0)) =
            checkpointState M (blockStart i)
              (checkpoint (currentIndex i)) := by
        rw [hindex, checkpointPosition_current i] at hcurrent
        exact hcurrent
      calc
        resumeScan M 0 (blockStop i)
            (checkpointState M 0 (checkpoint 0)) =
            resumeScan M 0 (blockStart i + blockCount i)
              (checkpointState M 0 (checkpoint 0)) := rfl
        _ = resumeScan M (blockStart i) (blockCount i)
              (resumeScan M 0 (blockStart i)
                (checkpointState M 0 (checkpoint 0))) := by
          simpa only [Nat.zero_add] using
            resumeScan_append M 0 (blockStart i) (blockCount i)
              (checkpointState M 0 (checkpoint 0))
        _ = resumeScan M (blockStart i) (blockCount i)
              (checkpointState M (blockStart i)
                (checkpoint (currentIndex i))) := by
          rw [hcurrent']
        _ = checkpointState M (blockStop i)
              (checkpoint (nextIndex i)) :=
          checkpointStateBlock M checkpoint hblocks i

theorem permanentGray_eq_of_checkpoints {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (checkpoint : Fin 129 → R) (expected : R)
    (hinitial : (GrayPermanentDP.initialState M).accumulator = checkpoint 0)
    (hblocks : ∀ i, CheckpointBlockStatement M checkpoint i)
    (hfinal : checkpoint ⟨128, by omega⟩ = expected) :
    GrayPermanentDP.permanentGray M = expected := by
  have hinitialState :
      GrayPermanentDP.initialState M = checkpointState M 0 (checkpoint 0) := by
    apply state_ext
    · exact initial_rowSums M
    · rfl
    · exact hinitial
  have hall := checkpointChain M checkpoint hblocks 128 (by omega)
  have hposition : checkpointPosition ⟨128, by omega⟩ = 16383 := by
    simp [checkpointPosition]
  rw [hposition] at hall
  unfold GrayPermanentDP.permanentGray
  change (GrayPermanentDP.run M 16383).accumulator = expected
  rw [run_eq_resumeScan, hinitialState, hall]
  simpa only [checkpointState] using hfinal

theorem permanent_eq_of_checkpoints {R : Type*} [CommRing R]
    (M : Matrix (Fin 14) (Fin 14) R)
    (checkpoint : Fin 129 → R) (expected : R)
    (hinitial : (GrayPermanentDP.initialState M).accumulator = checkpoint 0)
    (hblocks : ∀ i, CheckpointBlockStatement M checkpoint i)
    (hfinal : checkpoint ⟨128, by omega⟩ = expected) :
    Matrix.permanent M = expected := by
  rw [← GrayPermanentDP.permanentGray_eq_permanent]
  exact permanentGray_eq_of_checkpoints M checkpoint expected
    hinitial hblocks hfinal

end GrayCheckpointFramework
end SunCotangent
