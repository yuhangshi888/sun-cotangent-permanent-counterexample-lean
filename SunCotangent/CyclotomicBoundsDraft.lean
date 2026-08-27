import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace SunCotangent
namespace CyclotomicBounds

noncomputable section

abbrev Z29 := ZMod 29
abbrev Cyclic := AddMonoidAlgebra ℤ Z29

/-- The coefficientwise `ℓ¹` norm on the integral cyclic group ring. -/
def cyclicL1 (f : Cyclic) : ℤ :=
  ∑ e : Z29, |f.coeff e|

theorem cyclicL1_nonneg (f : Cyclic) : 0 ≤ cyclicL1 f := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem abs_coeff_le_cyclicL1 (f : Cyclic) (e : Z29) :
    |f.coeff e| ≤ cyclicL1 f := by
  classical
  exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (f.coeff i)) (Finset.mem_univ e)

theorem abs_coeff_sub_coeff_le_cyclicL1 (f : Cyclic) (e₁ e₂ : Z29)
    (hne : e₁ ≠ e₂) :
    |f.coeff e₁ - f.coeff e₂| ≤ cyclicL1 f := by
  calc
    |f.coeff e₁ - f.coeff e₂| ≤ |f.coeff e₁| + |f.coeff e₂| := abs_sub _ _
    _ = ∑ e ∈ ({e₁, e₂} : Finset Z29), |f.coeff e| := by
      rw [Finset.sum_pair hne]
    _ ≤ ∑ e : Z29, |f.coeff e| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro i _ _
        exact abs_nonneg _

theorem cyclicL1_add_le (f g : Cyclic) :
    cyclicL1 (f + g) ≤ cyclicL1 f + cyclicL1 g := by
  unfold cyclicL1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ abs_add_le (f.coeff i) (g.coeff i)

theorem cyclicL1_neg (f : Cyclic) : cyclicL1 (-f) = cyclicL1 f := by
  simp [cyclicL1]

theorem cyclicL1_sub_le (f g : Cyclic) :
    cyclicL1 (f - g) ≤ cyclicL1 f + cyclicL1 g := by
  rw [sub_eq_add_neg]
  exact (cyclicL1_add_le f (-g)).trans_eq (by rw [cyclicL1_neg])

@[simp]
theorem cyclicL1_single (e : Z29) (c : ℤ) :
    cyclicL1 (AddMonoidAlgebra.single e c) = |c| := by
  classical
  change (∑ x : Z29, |(Finsupp.single e c) x|) = |c|
  rw [Fintype.sum_eq_single e]
  · simp
  · intro x hxe
    simp [hxe]

theorem cyclicL1_le_card_mul (f : Cyclic) (C : ℤ)
    (h : ∀ e : Z29, |f.coeff e| ≤ C) :
    cyclicL1 f ≤ (Fintype.card Z29 : ℤ) * C := by
  unfold cyclicL1
  calc
    (∑ e : Z29, |f.coeff e|) ≤ ∑ _e : Z29, C :=
      Finset.sum_le_sum fun e _ ↦ h e
    _ = (Fintype.card Z29 : ℤ) * C := by simp

theorem coeff_mul_eq_sum (f g : Cyclic) (e : Z29) :
    (f * g).coeff e = ∑ a : Z29, f.coeff a * g.coeff (-a + e) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  rw [Finsupp.sum_fintype]
  intro a
  simp

theorem cyclicL1_mul_le (f g : Cyclic) :
    cyclicL1 (f * g) ≤ cyclicL1 f * cyclicL1 g := by
  unfold cyclicL1
  calc
    (∑ e : Z29, |(f * g).coeff e|) ≤
        ∑ e : Z29, ∑ a : Z29, |f.coeff a * g.coeff (-a + e)| := by
      exact Finset.sum_le_sum fun e _ ↦ by
        rw [coeff_mul_eq_sum]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Z29, |f.coeff a| * ∑ e : Z29, |g.coeff (-a + e)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [abs_mul]
    _ = ∑ a : Z29, |f.coeff a| * ∑ e : Z29, |g.coeff e| := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Fintype.sum_equiv (Equiv.addLeft (-a))
        (fun e : Z29 ↦ |g.coeff (-a + e)|)
        (fun e : Z29 ↦ |g.coeff e|) (fun _ ↦ rfl)
    _ = (∑ a : Z29, |f.coeff a|) * ∑ e : Z29, |g.coeff e| := by
      rw [Finset.sum_mul]

@[simp]
theorem cyclicL1_one : cyclicL1 (1 : Cyclic) = 1 := by
  rw [AddMonoidAlgebra.one_def, cyclicL1_single, abs_one]

theorem cyclicL1_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → Cyclic) :
    cyclicL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cyclicL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cyclicL1]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (cyclicL1_add_le _ _).trans (add_le_add (le_refl _) ih)

theorem cyclicL1_finset_prod_le {ι : Type*} (s : Finset ι) (f : ι → Cyclic) :
    cyclicL1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, cyclicL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (cyclicL1_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ih (cyclicL1_nonneg (f a)))

/-- The permanent of an `n × n` group-ring matrix has the expected
factorial-times-product `ℓ¹` bound. -/
theorem permanent_cyclicL1_le {n : ℕ} (M : Matrix (Fin n) (Fin n) Cyclic)
    (C : ℤ) (hM : ∀ i j, cyclicL1 (M i j) ≤ C) :
    cyclicL1 M.permanent ≤ (n.factorial : ℤ) * C ^ n := by
  classical
  rw [Matrix.permanent]
  calc
    cyclicL1 (∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, M (σ i) i) ≤
        ∑ σ : Equiv.Perm (Fin n), cyclicL1 (∏ i : Fin n, M (σ i) i) := by
      simpa using cyclicL1_finset_sum_le
        (Finset.univ : Finset (Equiv.Perm (Fin n)))
        (fun σ ↦ ∏ i : Fin n, M (σ i) i)
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), C ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      refine (cyclicL1_finset_prod_le (Finset.univ : Finset (Fin n))
        (fun i ↦ M (σ i) i)).trans ?_
      have hp :
          (∏ i : Fin n, cyclicL1 (M (σ i) i)) ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod
          (fun i _ ↦ cyclicL1_nonneg (M (σ i) i))
          (fun i _ ↦ hM (σ i) i)
      simpa using hp
    _ = (n.factorial : ℤ) * C ^ n := by
      simp [Fintype.card_perm]

/-! ## A fixed six-modulus CRT uniqueness lemma -/

def crtModulus : ℤ :=
  63_999_313_986_949_428_787_885_697_250_403_564_582_332_199_455_243_656_573

def broadCertificateBound : ℤ :=
  (Nat.factorial 14 : ℤ) * 29 ^ 29

def claimedCertificateInteger : ℤ :=
  -84_643_985_981_440 * 29 ^ 14

private theorem dvd_sub_of_zmod_eq (q : ℕ) (k N : ℤ)
    (h : (k : ZMod q) = (N : ZMod q)) : (q : ℤ) ∣ k - N := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa using sub_eq_zero.mpr h

/-- Six pairwise-coprime modular equalities, together with the coefficient
bound used in the paper, determine the integer uniquely. -/
theorem eq_claimed_of_six_zmod
    (k : ℤ)
    (hk : |k| ≤ broadCertificateBound)
    (h1 : (k : ZMod 1_999_998_457) = (claimedCertificateInteger : ZMod 1_999_998_457))
    (h2 : (k : ZMod 1_999_997_413) = (claimedCertificateInteger : ZMod 1_999_997_413))
    (h3 : (k : ZMod 1_999_996_949) = (claimedCertificateInteger : ZMod 1_999_996_949))
    (h4 : (k : ZMod 1_999_996_253) = (claimedCertificateInteger : ZMod 1_999_996_253))
    (h5 : (k : ZMod 1_999_996_021) = (claimedCertificateInteger : ZMod 1_999_996_021))
    (h6 : (k : ZMod 1_999_993_469) = (claimedCertificateInteger : ZMod 1_999_993_469)) :
    k = claimedCertificateInteger := by
  let d := k - claimedCertificateInteger
  have hd1 : (1_999_998_457 : ℤ) ∣ d := dvd_sub_of_zmod_eq _ _ _ h1
  have hd2 : (1_999_997_413 : ℤ) ∣ d := dvd_sub_of_zmod_eq _ _ _ h2
  have hd3 : (1_999_996_949 : ℤ) ∣ d := dvd_sub_of_zmod_eq _ _ _ h3
  have hd4 : (1_999_996_253 : ℤ) ∣ d := dvd_sub_of_zmod_eq _ _ _ h4
  have hd5 : (1_999_996_021 : ℤ) ∣ d := dvd_sub_of_zmod_eq _ _ _ h5
  have hd6 : (1_999_993_469 : ℤ) ∣ d := dvd_sub_of_zmod_eq _ _ _ h6
  have hd12 : ((1_999_998_457 : ℤ) * 1_999_997_413) ∣ d := by
    exact (by decide +kernel : IsCoprime (1_999_998_457 : ℤ) 1_999_997_413).mul_dvd hd1 hd2
  have hd123 : ((1_999_998_457 : ℤ) * 1_999_997_413 * 1_999_996_949) ∣ d := by
    exact (by decide +kernel : IsCoprime
      ((1_999_998_457 : ℤ) * 1_999_997_413) 1_999_996_949).mul_dvd hd12 hd3
  have hd1234 :
      ((1_999_998_457 : ℤ) * 1_999_997_413 * 1_999_996_949 * 1_999_996_253) ∣ d := by
    exact (by decide +kernel : IsCoprime
      ((1_999_998_457 : ℤ) * 1_999_997_413 * 1_999_996_949)
        1_999_996_253).mul_dvd hd123 hd4
  have hd12345 :
      ((1_999_998_457 : ℤ) * 1_999_997_413 * 1_999_996_949 * 1_999_996_253 *
        1_999_996_021) ∣ d := by
    exact (by decide +kernel : IsCoprime
      ((1_999_998_457 : ℤ) * 1_999_997_413 * 1_999_996_949 * 1_999_996_253)
        1_999_996_021).mul_dvd hd1234 hd5
  have hdQ : crtModulus ∣ d := by
    have := (by decide +kernel : IsCoprime
      ((1_999_998_457 : ℤ) * 1_999_997_413 * 1_999_996_949 * 1_999_996_253 *
        1_999_996_021) 1_999_993_469).mul_dvd hd12345 hd6
    norm_num [crtModulus] at this ⊢
    exact this
  have hd_abs : |d| < crtModulus := by
    calc
      |d| = |k - claimedCertificateInteger| := rfl
      _ ≤ |k| + |claimedCertificateInteger| := abs_sub _ _
      _ ≤ broadCertificateBound + |claimedCertificateInteger| :=
        add_le_add hk (le_refl _)
      _ < crtModulus := by norm_num [broadCertificateBound,
        claimedCertificateInteger, crtModulus, Nat.factorial]
  have hd_zero : d = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdQ
    simpa only [Int.natAbs_abs] using
      Int.natAbs_lt_natAbs_of_nonneg_of_lt (abs_nonneg d) hd_abs
  exact sub_eq_zero.mp hd_zero

end
end CyclotomicBounds
end SunCotangent
