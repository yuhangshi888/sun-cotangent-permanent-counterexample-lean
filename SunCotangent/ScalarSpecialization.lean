import SunCotangent.CyclotomicCertificate

/-!
# Direct scalar specializations of the cyclotomic certificate

This module contains only the generic algebraic bridge from the integral
cyclic-group-ring certificate to an ordinary scalar permanent over `ZMod q`.
It contains no concrete modulus, permanent value, checkpoint, or CRT
certificate.  Both the six-small-modulus computation and the independent
three-large-modulus computation import this common interface.
-/

open scoped BigOperators

namespace SunCotangent
namespace CyclotomicCertificate

noncomputable section

/-- The character used by `evalRoot` sends an exponent to the corresponding
ordinary power of the chosen root. -/
private theorem exponentHom_one (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1) :
    exponentHom w hw (Multiplicative.ofAdd (1 : Z29)) = w := by
  unfold exponentHom
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_toMultiplicativeLeft, toAdd_ofAdd]
  rw [show (1 : Z29) = ((1 : ℤ) : Z29) by norm_num,
    ZMod.lift_coe]
  change ((↑((rootUnit w hw) ^ (1 : ℤ)) : ZMod q)) = w
  simp [rootUnit]

@[simp]
theorem exponentHom_apply_pow (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1)
    (e : Z29) :
    exponentHom w hw (Multiplicative.ofAdd e) = w ^ e.val := by
  have he : e = e.val • (1 : Z29) := by
    simp [nsmul_eq_mul]
  calc
    exponentHom w hw (Multiplicative.ofAdd e) =
        exponentHom w hw
          (Multiplicative.ofAdd (e.val • (1 : Z29))) :=
      congrArg
        (fun a : Z29 ↦ exponentHom w hw (Multiplicative.ofAdd a)) he
    _ = exponentHom w hw
        ((Multiplicative.ofAdd (1 : Z29)) ^ e.val) := by
      rw [ofAdd_nsmul]
    _ = w ^ e.val := by
      rw [map_pow, exponentHom_one]

@[simp]
theorem evalRoot_monomial_pow (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1)
    (e : Z29) (c : ℤ) :
    evalRoot q w hw (monomial e c) = (c : ZMod q) * w ^ e.val := by
  rw [evalRoot_monomial, exponentHom_apply_pow, eq_intCast]

/-- A scalar power-sum certificate is enough to show that evaluation kills
the cyclotomic relation. -/
theorem evalRoot_cyclotomicSum_eq_zero
    (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1)
    (hsum : ∑ e : Z29, w ^ e.val = 0) :
    evalRoot q w hw cyclotomicSum = 0 := by
  rw [cyclotomicSum, map_sum]
  simpa only [evalRoot_monomial_pow, Int.cast_one, one_mul] using hsum

/-- Direct evaluation of the paired entry formula. -/
def scalarEntry (q : ℕ) (w : ZMod q) (e : Z29) : ZMod q :=
  ∑ r : Fin 14,
    ((2 * (r.val + 1 : ℤ) - 29 : ℤ) : ZMod q) *
      (w ^ (e * ((r.val + 1 : ℕ) : Z29)).val -
       w ^ (-e * ((r.val + 1 : ℕ) : Z29)).val)

/-- Direct evaluation of the centered quadratic-character Gauss sum. -/
def scalarGauss (q : ℕ) (w : ZMod q) : ZMod q :=
  ∑ e : Z29, (quadraticChar29 e : ZMod q) * w ^ e.val

/-- Evaluation of one integral paired entry is the direct scalar formula. -/
theorem evalRoot_entry (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1)
    (e : Z29) :
    evalRoot q w hw (entry e) = scalarEntry q w e := by
  unfold entry scalarEntry
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [map_sub, evalRoot_monomial_pow, evalRoot_monomial_pow]
  ring

private theorem gaussChar_eq_monomial_sum :
    gaussChar = ∑ e : Z29, monomial e (quadraticChar29 e) := by
  ext e
  change quadraticChar29 e =
    ∑ c : Z29, (Finsupp.single c (quadraticChar29 c)) e
  rw [Fintype.sum_eq_single e]
  · simp
  · intro c hce
    simp [hce]

/-- Evaluation of the centered Gauss representative is the direct scalar
Gauss sum. -/
theorem evalRoot_gaussChar (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1) :
    evalRoot q w hw gaussChar = scalarGauss q w := by
  rw [gaussChar_eq_monomial_sum, scalarGauss, map_sum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [evalRoot_monomial_pow]

/-- The scalar specialization of the full `14 × 14` group-ring matrix. -/
def scalarMatrix (q : ℕ) (w : ZMod q) :
    Matrix (Fin 14) (Fin 14) (ZMod q) :=
  fun i j ↦ scalarEntry q w
    (((i.val + 1 : ℕ) : Z29) * ((j.val + 1 : ℕ) : Z29))

theorem map_cyclotomicMatrix (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1) :
    cyclotomicMatrix.map (evalRoot q w hw).toRingHom = scalarMatrix q w := by
  ext i j
  simp only [Matrix.map_apply, cyclotomicMatrix, scalarMatrix]
  exact evalRoot_entry q w hw _

private theorem permanent_ringHom_map
    {R S ι : Type*} [CommSemiring R] [CommSemiring S] [Fintype ι]
    [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) :
    f (Matrix.permanent M) = Matrix.permanent (M.map f) := by
  classical
  simp only [Matrix.permanent, map_sum, map_prod, Matrix.map_apply]

/-- Evaluation commutes with the permanent and gives the scalar permanent. -/
theorem evalRoot_permanent (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1) :
    evalRoot q w hw (Matrix.permanent cyclotomicMatrix) =
      Matrix.permanent (scalarMatrix q w) := by
  change (evalRoot q w hw).toRingHom (Matrix.permanent cyclotomicMatrix) =
    Matrix.permanent (scalarMatrix q w)
  rw [permanent_ringHom_map (evalRoot q w hw).toRingHom cyclotomicMatrix,
    map_cyclotomicMatrix]

/-- The group-ring certificate specializes to the scalar product computed
in each finite ring. -/
theorem evalRoot_certificatePolynomial_scalar
    (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1) :
    evalRoot q w hw certificatePolynomial =
      scalarGauss q w * Matrix.permanent (scalarMatrix q w) := by
  rw [certificatePolynomial, map_mul, evalRoot_gaussChar,
    evalRoot_permanent]

/-- Generic light-weight postprocessing: once a scalar permanent value is
known, the corresponding modular equality for `canonicalConstant` follows
without repeating the permanent computation. -/
theorem canonicalConstant_mod_of_scalar_certificate
    (q : ℕ) (w : ZMod q) (hw : w ^ 29 = 1)
    (hcyclotomic : evalRoot q w hw cyclotomicSum = 0)
    (M : Matrix (Fin 14) (Fin 14) (ZMod q))
    (hM : scalarMatrix q w = M)
    (g p r : ZMod q)
    (hgauss : scalarGauss q w = g)
    (hpermanent : Matrix.permanent M = p)
    (hproduct : g * p = r)
    (hresidue : r = (certificateInteger : ZMod q)) :
    (canonicalConstant : ZMod q) = (certificateInteger : ZMod q) := by
  calc
    (canonicalConstant : ZMod q) = r :=
      canonicalConstant_mod_eq_of_evalRoot_eq q w hw hcyclotomic r (by
        rw [evalRoot_certificatePolynomial_scalar, hM, hgauss, hpermanent]
        exact hproduct)
    _ = (certificateInteger : ZMod q) := hresidue

end
end CyclotomicCertificate
end SunCotangent
