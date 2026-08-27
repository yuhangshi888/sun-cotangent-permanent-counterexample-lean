import Mathlib.Algebra.Field.GeomSum
import SunCotangent.AnalyticBridge
import SunCotangent.CyclotomicCertificate

/-!
# Complex specialization of the cyclotomic certificate

This file evaluates the integral cyclic-group-ring certificate at the fixed
primitive root `zeta29`.  It supplies the exact bridge between the finite
coefficient certificate in `CyclotomicCertificate` and the analytic statement
required by `AnalyticBridge`.

The only input from the finite certificate not proved here is the final
coefficient computation `canonicalConstant = certificateInteger`.  It is kept
as an explicit hypothesis in the last theorem until the CRT module exports its
unconditional theorem under a stable name.
-/

open scoped BigOperators

open Finset

namespace SunCotangent
namespace CertificateComplexBridge

open CyclotomicCertificate

noncomputable section

local instance primeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- Evaluation of the integral cyclic group ring at the standard complex
twenty-ninth root of unity. -/
def evalZeta29 : Cyclic ℤ →ₐ[ℤ] ℂ :=
  AddMonoidAlgebra.lift ℤ ℂ Z29 psi29.toMonoidHom

@[simp]
theorem evalZeta29_monomial (e : Z29) (c : ℤ) :
    evalZeta29 (monomial e c) = (c : ℂ) * zeta29 ^ e.val := by
  have hpsi : psi29 e = zeta29 ^ e.val := rfl
  rw [evalZeta29, monomial, AddMonoidAlgebra.lift_single]
  rw [Algebra.smul_def]
  change (c : ℂ) * psi29 e = (c : ℂ) * zeta29 ^ e.val
  exact congrArg (fun z : ℂ ↦ (c : ℂ) * z) hpsi

/-- Evaluation kills the cyclotomic relation. -/
@[simp]
theorem evalZeta29_cyclotomicSum : evalZeta29 cyclotomicSum = 0 := by
  rw [cyclotomicSum, map_sum]
  simp only [evalZeta29_monomial, Int.cast_one, one_mul]
  simpa only [psi29, AddChar.zmodChar_apply] using
    (AddChar.sum_eq_zero_of_ne_one psi29_ne_one)

/-- The root associated with a product in `ZMod 29` is the corresponding
power of the root associated with the first factor. -/
private theorem zeta29_pow_zmod_mul (e : Z29) (n : ℕ) :
    zeta29 ^ (e * (n : Z29)).val = (zeta29 ^ e.val) ^ n := by
  change psi29 (e * (n : Z29)) = psi29 e ^ n
  rw [show e * (n : Z29) = n • e by simp [nsmul_eq_mul, mul_comm]]
  exact psi29.map_nsmul_eq_pow n e

/-- The negative exponent used in the paired representative is the
complementary positive exponent. -/
private theorem zeta29_pow_neg_zmod_mul (e : Z29) (n : ℕ) (hn : n ≤ 29) :
    zeta29 ^ (-e * (n : Z29)).val =
      (zeta29 ^ e.val) ^ (29 - n) := by
  rw [show -e * (n : Z29) = e * ((29 - n : ℕ) : Z29) by
    have hcomp : (((29 - n : ℕ) : Z29)) = -(n : Z29) := by
      rw [Nat.cast_sub hn, ZMod.natCast_self]
      ring
    rw [hcomp]
    ring]
  exact zeta29_pow_zmod_mul e (29 - n)

/-- Passing from a natural exponent to its residue modulo `29` does not
change the corresponding power of `zeta29`. -/
private theorem zeta29_pow_zmod_natCast (n : ℕ) :
    zeta29 ^ (n : Z29).val = zeta29 ^ n := by
  rw [ZMod.val_natCast]
  exact (zeta29_pow_eq_pow_mod n).symm

/-- The geometric sum of all twenty-nine powers vanishes at every nontrivial
twenty-ninth root. -/
private theorem geomSum29_eq_zero (t : ℂ) (ht : t ^ 29 = 1) (ht1 : t ≠ 1) :
    ∑ i ∈ Finset.range 29, t ^ i = 0 := by
  rw [geom_sum_eq ht1, ht]
  norm_num

/-- The paired `14`-term representative and the paper's weighted `28`-term
representative agree at a nontrivial twenty-ninth root.  Their difference is
exactly `27` times the geometric sum. -/
private theorem pairedSum_eq_paperSum (t : ℂ)
    (hgeom : ∑ i ∈ Finset.range 29, t ^ i = 0) :
    (∑ r : Fin 14,
        ((2 * (r.val + 1 : ℤ) - 29 : ℤ) : ℂ) *
          (t ^ (r.val + 1) - t ^ (29 - (r.val + 1)))) =
      (29 : ℂ) - 2 *
        ∑ s : Fin 28, ((28 - (s.val : ℤ) : ℤ) : ℂ) * t ^ s.val := by
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ] at hgeom ⊢
  linear_combination 27 * hgeom

/-- The weighted sum occurring in `paperEntry` evaluates to the required
rational root expression. -/
private theorem paperSum_eq_rootRatio (t : ℂ) (ht : t ^ 29 = 1) (ht1 : t ≠ 1) :
    (29 : ℂ) - 2 *
        ∑ s : Fin 28, ((28 - (s.val : ℤ) : ℤ) : ℂ) * t ^ s.val =
      29 * rootRatio t := by
  have hgeom := geomSum29_eq_zero t ht ht1
  have hweighted :
      (t - 1) *
          (∑ s : Fin 28,
            ((28 - (s.val : ℤ) : ℤ) : ℂ) * t ^ s.val) = -29 := by
    norm_num [Fin.sum_univ_succ, Finset.sum_range_succ] at hgeom ⊢
    linear_combination hgeom
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  change (29 : ℂ) - 2 *
      (∑ s : Fin 28,
        ((28 - (s.val : ℤ) : ℤ) : ℂ) * t ^ s.val) =
    29 * ((t + 1) / (t - 1))
  rw [← mul_div_assoc, eq_div_iff hden]
  calc
    ((29 : ℂ) - 2 *
        (∑ s : Fin 28,
          ((28 - (s.val : ℤ) : ℤ) : ℂ) * t ^ s.val)) * (t - 1) =
        29 * (t - 1) - 2 *
          ((t - 1) *
            ∑ s : Fin 28,
              ((28 - (s.val : ℤ) : ℤ) : ℂ) * t ^ s.val) := by ring
    _ = 29 * (t + 1) := by rw [hweighted]; ring

/-- Explicit evaluation of the antisymmetric group-ring representative. -/
theorem evalZeta29_entry_formula (e : Z29) :
    evalZeta29 (entry e) =
      ∑ r : Fin 14,
        ((2 * (r.val + 1 : ℤ) - 29 : ℤ) : ℂ) *
          ((zeta29 ^ e.val) ^ (r.val + 1) -
            (zeta29 ^ e.val) ^ (29 - (r.val + 1))) := by
  rw [entry, map_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [map_sub, evalZeta29_monomial, evalZeta29_monomial,
    zeta29_pow_zmod_mul,
    zeta29_pow_neg_zmod_mul e (r.val + 1) (by omega)]
  ring

/-- Every nonzero group-ring exponent specializes to `29` times the analytic
root ratio. -/
theorem evalZeta29_entry (e : Z29) (he : e ≠ 0) :
    evalZeta29 (entry e) = 29 * rootRatio (zeta29 ^ e.val) := by
  let t : ℂ := zeta29 ^ e.val
  have ht : t ^ 29 = 1 := by
    dsimp [t]
    rw [← pow_mul, Nat.mul_comm, pow_mul, zeta29_pow_twentyNine, one_pow]
  have ht1 : t ≠ 1 := by
    dsimp [t]
    exact zeta29_pow_ne_one
      (Nat.not_dvd_of_pos_of_lt (ZMod.val_pos.mpr he) e.val_lt)
  rw [evalZeta29_entry_formula]
  change (∑ r : Fin 14,
      ((2 * (r.val + 1 : ℤ) - 29 : ℤ) : ℂ) *
        (t ^ (r.val + 1) - t ^ (29 - (r.val + 1)))) =
    29 * rootRatio t
  rw [pairedSum_eq_paperSum t (geomSum29_eq_zero t ht ht1)]
  exact paperSum_eq_rootRatio t ht ht1

/-- The custom Euler-criterion character used by the finite certificate is
the same quadratic character as Mathlib's. -/
private theorem quadraticChar29_eq_mathlib :
    ∀ e : Z29, quadraticChar29 e = quadraticChar (ZMod 29) e := by
  decide +kernel

/-- The centered character representative evaluates to the analytic Gauss
sum `gauss29`. -/
theorem evalZeta29_gaussChar : evalZeta29 gaussChar = gauss29 := by
  have hsum : gaussChar =
      ∑ e : Z29, monomial e (quadraticChar29 e) := by
    ext x
    rw [gaussChar_coeff]
    change quadraticChar29 x =
      ∑ e : Z29, (monomial e (quadraticChar29 e)).coeff x
    rw [Finset.sum_eq_single x]
    · simp [monomial]
    · intro e _he hex
      simp [monomial, hex]
    · simp
  rw [hsum, map_sum, gauss29_eq_gaussSum, gaussSum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [evalZeta29_monomial, quadraticChar29_eq_mathlib]
  rfl

/-- All exponents occurring in the `14 × 14` matrix are nonzero modulo
`29`. -/
private theorem matrixExponent_ne_zero (j k : Half29) :
    (((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29)) ≠ 0 := by
  apply mul_ne_zero
  · rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  · rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/-- Entrywise specialization of the integral cyclotomic matrix is exactly
the analytically defined scaled root matrix. -/
theorem map_cyclotomicMatrix :
    cyclotomicMatrix.map evalZeta29.toRingHom = scaledRootMatrix29 := by
  ext j k
  change evalZeta29 (cyclotomicMatrix j k) = scaledRootMatrix29 j k
  rw [cyclotomicMatrix,
    evalZeta29_entry _ (matrixExponent_ne_zero j k)]
  have hexponent :
      ((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29) =
        (((j.val + 1) * (k.val + 1) : ℕ) : Z29) := by
    push_cast
    ring
  rw [hexponent, zeta29_pow_zmod_natCast]
  simp [scaledRootMatrix29, rootMatrix29, Matrix.smul_apply, smul_eq_mul]

/-- Evaluation commutes with the permanent of the cyclotomic matrix. -/
theorem evalZeta29_permanent :
    evalZeta29 (Matrix.permanent cyclotomicMatrix) =
      scaledRootMatrix29.permanent := by
  calc
    evalZeta29 (Matrix.permanent cyclotomicMatrix) =
        (cyclotomicMatrix.map evalZeta29.toRingHom).permanent := by
      change evalZeta29.toRingHom (Matrix.permanent cyclotomicMatrix) = _
      exact (permanent_map evalZeta29.toRingHom cyclotomicMatrix).symm
    _ = scaledRootMatrix29.permanent := by rw [map_cyclotomicMatrix]

/-- Evaluation of the full group-ring certificate is its analytic complex
left-hand side. -/
theorem evalZeta29_certificatePolynomial :
    evalZeta29 certificatePolynomial =
      gauss29 * scaledRootMatrix29.permanent := by
  rw [certificatePolynomial, map_mul, evalZeta29_gaussChar,
    evalZeta29_permanent]

/-- The complete algebraic-to-analytic implication.  The hypothesis is the
single integer equality discharged by the six-modulus CRT computation. -/
theorem complex_certificate_of_canonicalConstant
    (hcanonical : canonicalConstant = certificateInteger) :
    gauss29 * scaledRootMatrix29.permanent =
      -(84643985981440 : ℂ) * (29 : ℂ) ^ 14 := by
  calc
    gauss29 * scaledRootMatrix29.permanent =
        evalZeta29 certificatePolynomial :=
      evalZeta29_certificatePolynomial.symm
    _ = evalZeta29
        (monomial 0 canonicalConstant +
          certificatePolynomial.coeff (28 : Z29) • cyclotomicSum) := by
      exact congrArg (fun f : Cyclic ℤ ↦ evalZeta29 f)
        certificatePolynomial_normalForm
    _ = (certificateInteger : ℂ) := by
      simp [hcanonical]
    _ = -(84643985981440 : ℂ) * (29 : ℂ) ^ 14 := by
      norm_num [certificateInteger]

end
end CertificateComplexBridge
end SunCotangent
