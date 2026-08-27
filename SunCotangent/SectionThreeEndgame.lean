import SunCotangent.ArchimedeanCertificate
import SunCotangent.CertificateComplexBridge
import SunCotangent.EagerModPack
import SunCotangent.ScalarFiniteFieldCertificate

/-!
# The independent Section 3 endgame

This file isolates the logical content of Section 3 of the paper.  Its only
analytic arithmetic input is an *integer witness*

`(z : ℝ) = √29 * permanent(realCotMatrix29)`.

The cyclotomic normal form first identifies its canonical integral
coefficient with `-z * 29^14`.  Direct specialization of that identity at
the first three roots in Table 1 then gives the three residues of `z`.
The table computation, the three-modulus CRT, and the Archimedean estimate
finally determine `z` uniquely.

In particular, none of the proofs below obtains a Table 1 residue by first
substituting the claimed final integer into `certificateInteger`.
-/

namespace SunCotangent
namespace SectionThreeEndgame

open CyclotomicCertificate

noncomputable section

local instance q1PrimeFact : Fact (Nat.Prime q1) :=
  ⟨ScalarFiniteFieldCertificate.q1_prime⟩
local instance q2PrimeFact : Fact (Nat.Prime q2) :=
  ⟨ScalarFiniteFieldCertificate.q2_prime⟩
local instance q3PrimeFact : Fact (Nat.Prime q3) :=
  ⟨ScalarFiniteFieldCertificate.q3_prime⟩

/-! ## From an integral analytic value to the canonical coefficient -/

/-- If the analytic cotangent permanent is represented by the integer `z`,
then the canonical coefficient of the integral cyclotomic certificate is
exactly `-z * 29^14`.

This statement does not use the claimed numerical value of `z`, nor any
finite-field permanent computation. -/
theorem canonicalConstant_eq_neg_integer_mul_twentyNine_pow
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent) :
    canonicalConstant = -z * 29 ^ 14 := by
  have hcot :
      ((realCotMatrix29.permanent : ℝ) : ℂ) =
        -rootMatrix29.permanent := by
    calc
      ((realCotMatrix29.permanent : ℝ) : ℂ) =
          cotMatrix29.permanent := ofReal_permanent_realCotMatrix29
      _ = -rootMatrix29.permanent := permanent_cotMatrix29
  have hroot :
      rootMatrix29.permanent =
        -((realCotMatrix29.permanent : ℝ) : ℂ) := by
    calc
      rootMatrix29.permanent = -(-rootMatrix29.permanent) := by ring
      _ = -((realCotMatrix29.permanent : ℝ) : ℂ) := by rw [← hcot]
  have hcanonicalComplex :
      (canonicalConstant : ℂ) =
        gauss29 * scaledRootMatrix29.permanent := by
    calc
      (canonicalConstant : ℂ) =
          CertificateComplexBridge.evalZeta29
            (monomial 0 canonicalConstant +
              certificatePolynomial.coeff (28 : Z29) • cyclotomicSum) := by
            simp [CertificateComplexBridge.evalZeta29_monomial]
      _ = CertificateComplexBridge.evalZeta29 certificatePolynomial := by
        exact congrArg
          (fun f : Cyclic ℤ ↦ CertificateComplexBridge.evalZeta29 f)
          certificatePolynomial_normalForm.symm
      _ = gauss29 * scaledRootMatrix29.permanent :=
        CertificateComplexBridge.evalZeta29_certificatePolynomial
  have hanalyticComplex :
      gauss29 * scaledRootMatrix29.permanent =
        ((-z * 29 ^ 14 : ℤ) : ℂ) := by
    calc
      gauss29 * scaledRootMatrix29.permanent =
          (((Real.sqrt 29 : ℝ) : ℂ)) *
            ((29 : ℂ) ^ 14 * rootMatrix29.permanent) := by
        rw [gauss29_eq_sqrt, permanent_scaledRootMatrix29]
      _ = -(29 : ℂ) ^ 14 *
          (((Real.sqrt 29 * realCotMatrix29.permanent : ℝ) : ℂ)) := by
        rw [hroot]
        push_cast
        ring
      _ = -(29 : ℂ) ^ 14 * (((z : ℝ) : ℂ)) := by rw [← hreal]
      _ = ((-z * 29 ^ 14 : ℤ) : ℂ) := by
        push_cast
        ring
  exact Int.cast_injective (hcanonicalComplex.trans hanalyticComplex)

/-! ## Direct finite-field specialization -/

/-- Generic cancellation step behind each of the three Table 1 rows.

The canonical coefficient is evaluated directly in the finite field.  The
scaled matrix identity contributes `29^14`, which is then cancelled. -/
private theorem intCast_eq_finiteTPrimeResidue_of_data
    (q : ℕ) [Fact (Nat.Prime q)] (w : ZMod q) (z : ℤ)
    (hcanonical : canonicalConstant = -z * 29 ^ 14)
    (hw : w ^ 29 = 1)
    (hcyclotomic : evalRoot q w hw cyclotomicSum = 0)
    (hscalarMatrix : scalarMatrix q w =
      (29 : ZMod q) • ScalarFiniteFieldCertificate.literalRMatrix q w)
    (h29pow : (29 : ZMod q) ^ 14 ≠ 0) :
    (z : ZMod q) = ScalarFiniteFieldCertificate.finiteTPrimeResidue q w := by
  have hcanonicalMod :
      (canonicalConstant : ZMod q) =
        -(z : ZMod q) * (29 : ZMod q) ^ 14 := by
    calc
      (canonicalConstant : ZMod q) =
          ((-z * 29 ^ 14 : ℤ) : ZMod q) :=
        congrArg (fun n : ℤ ↦ (n : ZMod q)) hcanonical
      _ = -(z : ZMod q) * (29 : ZMod q) ^ 14 := by
        simp only [Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_ofNat]
  have heval :
      (canonicalConstant : ZMod q) =
        scalarGauss q w * Matrix.permanent (scalarMatrix q w) := by
    calc
      (canonicalConstant : ZMod q) =
          evalRoot q w hw certificatePolynomial :=
        (evalRoot_certificatePolynomial_eq_canonicalConstant
          q w hw hcyclotomic).symm
      _ = scalarGauss q w * Matrix.permanent (scalarMatrix q w) :=
        evalRoot_certificatePolynomial_scalar q w hw
  have hpermanentScale :
      Matrix.permanent (scalarMatrix q w) =
        (29 : ZMod q) ^ 14 *
          Matrix.permanent (ScalarFiniteFieldCertificate.literalRMatrix q w) := by
    rw [hscalarMatrix, Matrix.permanent_smul, Fintype.card_fin]
  apply mul_left_cancel₀ h29pow
  calc
    (29 : ZMod q) ^ 14 * (z : ZMod q) =
        -(canonicalConstant : ZMod q) := by
      rw [hcanonicalMod]
      ring
    _ = -(scalarGauss q w *
        Matrix.permanent (scalarMatrix q w)) := by rw [heval]
    _ = (29 : ZMod q) ^ 14 *
        (-ScalarFiniteFieldCertificate.literalGauss q w *
          Matrix.permanent (ScalarFiniteFieldCertificate.literalRMatrix q w)) := by
      rw [hpermanentScale,
        ← ScalarFiniteFieldCertificate.literalGauss_eq_scalarGauss]
      ring
    _ = (29 : ZMod q) ^ 14 *
        ScalarFiniteFieldCertificate.finiteTPrimeResidue q w := by
      rfl

/-- The integral analytic value specializes to the first finite expression
`-G_q permanent(R_q)` from equation (3.1). -/
theorem intCast_q1_eq_finiteTPrimeResidue
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent) :
    (z : ZMod q1) =
      ScalarFiniteFieldCertificate.finiteTPrimeResidue q1 w1 := by
  apply intCast_eq_finiteTPrimeResidue_of_data q1 w1 z
    (canonicalConstant_eq_neg_integer_mul_twentyNine_pow z hreal)
    root1 evalRoot_cyclotomicSum1
  · rw [scalarMatrix1_eq_residueMatrix1,
      ScalarFiniteFieldCertificate.residueMatrix1_eq_scaled_literalR]
  · unfold q1
    reduce_mod_char
    decide +kernel

/-- The corresponding direct specialization at the second Table 1 root. -/
theorem intCast_q2_eq_finiteTPrimeResidue
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent) :
    (z : ZMod q2) =
      ScalarFiniteFieldCertificate.finiteTPrimeResidue q2 w2 := by
  apply intCast_eq_finiteTPrimeResidue_of_data q2 w2 z
    (canonicalConstant_eq_neg_integer_mul_twentyNine_pow z hreal)
    root2 evalRoot_cyclotomicSum2
  · rw [scalarMatrix2_eq_residueMatrix2,
      ScalarFiniteFieldCertificate.residueMatrix2_eq_scaled_literalR]
  · unfold q2
    reduce_mod_char
    decide +kernel

/-- The corresponding direct specialization at the third Table 1 root. -/
theorem intCast_q3_eq_finiteTPrimeResidue
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent) :
    (z : ZMod q3) =
      ScalarFiniteFieldCertificate.finiteTPrimeResidue q3 w3 := by
  apply intCast_eq_finiteTPrimeResidue_of_data q3 w3 z
    (canonicalConstant_eq_neg_integer_mul_twentyNine_pow z hreal)
    root3 evalRoot_cyclotomicSum3
  · rw [scalarMatrix3_eq_residueMatrix3,
      ScalarFiniteFieldCertificate.residueMatrix3_eq_scaled_literalR]
  · unfold q3
    reduce_mod_char
    decide +kernel

/-! ## Table 1, CRT, and Archimedean uniqueness -/

/-- The representative `N` selected in equation (3.2) is the centered
representative modulo the three-prime product. -/
theorem sectionThreeN_is_centered :
    2 * |ScalarFiniteFieldCertificate.sectionThreeN| <
      ScalarFiniteFieldCertificate.sectionThreeModulus := by
  norm_num [ScalarFiniteFieldCertificate.sectionThreeN,
    ScalarFiniteFieldCertificate.sectionThreeModulus, q1, q2, q3]

theorem intCast_q1_eq_table1Residue_of_pack
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    (z : ZMod q1) = (51_284_286 : ZMod q1) := by
  exact (intCast_q1_eq_finiteTPrimeResidue z hreal).trans
    (ScalarFiniteFieldCertificate.table1_tPrimeResidue_q1_of_scaled
      (permanent1_of_pack hpack))

theorem intCast_q2_eq_table1Residue_of_pack
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    (z : ZMod q2) = (95_468_454 : ZMod q2) := by
  exact (intCast_q2_eq_finiteTPrimeResidue z hreal).trans
    (ScalarFiniteFieldCertificate.table1_tPrimeResidue_q2_of_scaled
      (permanent2_of_pack hpack))

theorem intCast_q3_eq_table1Residue_of_pack
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    (z : ZMod q3) = (115_105_862 : ZMod q3) := by
  exact (intCast_q3_eq_finiteTPrimeResidue z hreal).trans
    (ScalarFiniteFieldCertificate.table1_tPrimeResidue_q3_of_scaled
      (permanent3_of_pack hpack))

/-- The three literal Table 1 computations reconstruct the integer witness
modulo the product of the three primes. -/
theorem integerWitness_modEq_sectionThreeN_of_pack
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    z ≡ ScalarFiniteFieldCertificate.sectionThreeN
      [ZMOD ScalarFiniteFieldCertificate.sectionThreeModulus] := by
  exact ScalarFiniteFieldCertificate.sectionThree_crt_congruence z
    (intCast_q1_eq_table1Residue_of_pack z hreal hpack)
    (intCast_q2_eq_table1Residue_of_pack z hreal hpack)
    (intCast_q3_eq_table1Residue_of_pack z hreal hpack)

/-- Section 3 determines every integral analytic witness uniquely. -/
theorem integerWitness_eq_claimed_of_pack
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    z = ArchimedeanCertificate.paperClaimedValue := by
  have hsection := integerWitness_modEq_sectionThreeN_of_pack z hreal hpack
  have hpaper : z ≡ ArchimedeanCertificate.paperClaimedValue
      [ZMOD ArchimedeanCertificate.paperCRTModulus] := by
    simpa [ScalarFiniteFieldCertificate.sectionThreeN,
      ScalarFiniteFieldCertificate.sectionThreeModulus,
      ArchimedeanCertificate.paperClaimedValue,
      ArchimedeanCertificate.paperCRTModulus, q1, q2, q3] using hsection
  exact ArchimedeanCertificate.eq_paperClaimedValue_of_modEq_of_cotangent_identity
    z hpaper hreal

/-- Explicit formulation of the Section 3 dependency on Sun's integrality
application: once that application supplies an integer witness, the checked
packed permanent certificate proves the exact analytic value. -/
theorem exact_value_of_integral_witness_and_pack
    (z : ℤ)
    (hreal : (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Real.sqrt 29 * realCotMatrix29.permanent = 84_643_985_981_440 := by
  rw [← hreal, integerWitness_eq_claimed_of_pack z hreal hpack]
  rfl

/-- Existential form: this theorem exposes integrality as the sole imported
mathematical assertion needed by the independent Section 3 route. -/
theorem exact_value_of_integrality_and_pack
    (hintegral : ∃ z : ℤ, (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (hpack : Matrix.permanent packMatrix = expectedPermanentPack) :
    Real.sqrt 29 * realCotMatrix29.permanent = 84_643_985_981_440 := by
  obtain ⟨z, hreal⟩ := hintegral
  exact exact_value_of_integral_witness_and_pack z hreal hpack

/-- The strict nested-product certificate can feed the independent Section 3
route without importing the long checkpoint evaluator into this file. -/
theorem exact_value_of_integrality_and_eagerCertificate
    (hintegral : ∃ z : ℤ, (z : ℝ) =
      Real.sqrt 29 * realCotMatrix29.permanent)
    (heager : Matrix.permanent eagerPackMatrix = expectedEagerPermanent) :
    Real.sqrt 29 * realCotMatrix29.permanent = 84_643_985_981_440 := by
  exact exact_value_of_integrality_and_pack hintegral
    (packPermanent_of_eagerPermanent heager)

end
end SectionThreeEndgame
end SunCotangent
