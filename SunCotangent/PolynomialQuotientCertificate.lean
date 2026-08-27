import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import SunCotangent.LiteralCyclotomicCertificate

/-!
# Equation (4.1) in the literal polynomial quotient

This file transports the already proved cyclic-group-ring certificate into
the quotient `ℤ[X] / (Φ₂₉)`, and then identifies every transported term with
the polynomial printed in Section 4 of the paper.
-/

open scoped BigOperators

namespace SunCotangent
namespace PolynomialQuotientCertificate

open Polynomial
open CyclotomicCertificate

noncomputable section

local instance primeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- The literal coefficient ring `ℤ[X] / (Φ₂₉)`. -/
abbrev PolynomialCyclotomicRing :=
  ℤ[X] ⧸ Ideal.span ({Polynomial.cyclotomic 29 ℤ} : Set ℤ[X])

/-- The quotient map `ℤ[X] → ℤ[X] / (Φ₂₉)`. -/
def polynomialQuotientMap : ℤ[X] →+* PolynomialCyclotomicRing :=
  Ideal.Quotient.mk (Ideal.span
    ({Polynomial.cyclotomic 29 ℤ} : Set ℤ[X]))

/-- The class of `X` in the literal polynomial quotient. -/
def quotientX : PolynomialCyclotomicRing :=
  polynomialQuotientMap X

theorem quotientX_pow_twentyNine : quotientX ^ 29 = 1 := by
  have hzero : polynomialQuotientMap (X ^ 29 - 1) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← Polynomial.cyclotomic_prime_mul_X_sub_one ℤ 29]
    exact Ideal.mul_mem_right (X - 1)
      (Ideal.span ({Polynomial.cyclotomic 29 ℤ} : Set ℤ[X]))
      (Ideal.mem_span_singleton_self (Polynomial.cyclotomic 29 ℤ))
  have heq : polynomialQuotientMap (X ^ 29) = polynomialQuotientMap 1 := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using hzero
  calc
    quotientX ^ 29 = polynomialQuotientMap (X ^ 29) := by
      exact (map_pow polynomialQuotientMap X 29).symm
    _ = polynomialQuotientMap 1 := heq
    _ = 1 := map_one polynomialQuotientMap

/-- Evaluation of the cyclic group ring at the class of `X`. -/
def cyclicToPolynomialQuotient :
    Cyclic ℤ →ₐ[ℤ] PolynomialCyclotomicRing :=
  AddMonoidAlgebra.lift ℤ PolynomialCyclotomicRing Z29
    (exponentHom quotientX quotientX_pow_twentyNine)

private theorem exponentHom_one_generic
    {R : Type*} [CommRing R] (w : R) (hw : w ^ 29 = 1) :
    exponentHom w hw (Multiplicative.ofAdd (1 : Z29)) = w := by
  unfold exponentHom
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_toMultiplicativeLeft, toAdd_ofAdd]
  rw [show (1 : Z29) = ((1 : ℤ) : Z29) by norm_num,
    ZMod.lift_coe]
  change ↑((rootUnit w hw) ^ (1 : ℤ)) = w
  simp [rootUnit]

private theorem exponentHom_apply_pow_generic
    {R : Type*} [CommRing R] (w : R) (hw : w ^ 29 = 1)
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
      rw [map_pow, exponentHom_one_generic]

@[simp]
theorem cyclicToPolynomialQuotient_monomial (e : Z29) (c : ℤ) :
    cyclicToPolynomialQuotient (CyclotomicCertificate.monomial e c) =
      (c : PolynomialCyclotomicRing) * quotientX ^ e.val := by
  unfold CyclotomicCertificate.monomial
  rw [cyclicToPolynomialQuotient, AddMonoidAlgebra.lift_single,
    exponentHom_apply_pow_generic]
  simp [Algebra.smul_def]

/-! ## The literal Section 4 polynomials -/

/-- The polynomial
`U(Y) = ∑_(s=0)^27 (28-s)Y^s`, evaluated in the literal quotient. -/
def sectionFourU (Y : PolynomialCyclotomicRing) :
    PolynomialCyclotomicRing :=
  ∑ s : Fin 28,
    ((28 - (s.val : ℤ) : ℤ) : PolynomialCyclotomicRing) * Y ^ s.val

/-- The paper's entry `A_e(X) = 29 - 2 U(X^e)`, with its exponent kept as
the unreduced natural number printed in the paper. -/
def sectionFourAEntry (e : ℕ) : PolynomialCyclotomicRing :=
  (29 : PolynomialCyclotomicRing) -
    2 • sectionFourU (quotientX ^ e)

/-- The literal `14 × 14` matrix `A(X) = (A_{jk}(X))` from Section 4. -/
def sectionFourMatrix :
    Matrix (Fin 14) (Fin 14) PolynomialCyclotomicRing :=
  fun j k ↦ sectionFourAEntry
    ((j.val + 1) * (k.val + 1))

/-- The literal Gauss polynomial
`𝒢(X) = ∑_(a=0)^28 X^(a²)` in the polynomial quotient. -/
def sectionFourGauss : PolynomialCyclotomicRing :=
  ∑ a : Fin 29, quotientX ^ (a.val ^ 2)

/-- A raw natural exponent and its residue modulo `29` give the same power
of `X` in the literal polynomial quotient. -/
theorem quotientX_pow_natCast_val (n : ℕ) :
    quotientX ^ ((n : Z29).val) = quotientX ^ n := by
  symm
  calc
    quotientX ^ n = quotientX ^ (n % 29) :=
      pow_eq_pow_mod n quotientX_pow_twentyNine
    _ = quotientX ^ ((n : Z29).val) := by
      rw [ZMod.val_natCast]

/-- Exponents may be reduced modulo `29` in the literal quotient.  This is
the only exponent-reduction fact needed to identify `U(X^e)` with its cyclic
group-ring representative. -/
theorem quotientX_pow_zmod_mul (e : Z29) (s : Fin 28) :
    quotientX ^ (e * (s.val : Z29)).val =
      (quotientX ^ e.val) ^ s.val := by
  symm
  calc
    (quotientX ^ e.val) ^ s.val =
        quotientX ^ (e.val * s.val) :=
      (pow_mul quotientX e.val s.val).symm
    _ = quotientX ^ ((e.val * s.val) % 29) :=
      pow_eq_pow_mod (e.val * s.val) quotientX_pow_twentyNine
    _ = quotientX ^ (e * (s.val : Z29)).val := by
      rw [ZMod.val_mul,
        ZMod.val_natCast_of_lt
          (s.isLt.trans (by norm_num : 28 < 29))]

/-- Squaring an index in `ZMod 29` and then taking its canonical value gives
the same quotient power as the unreduced natural square printed in
`𝒢(X)`. -/
theorem quotientX_pow_zmod_sq (a : Z29) :
    quotientX ^ (a ^ 2).val = quotientX ^ (a.val ^ 2) := by
  have ha : ((a.val ^ 2 : ℕ) : Z29) = a ^ 2 := by
    simp only [Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [← ha, quotientX_pow_natCast_val]

/-- Evaluation of the cyclic representative `U e` is literally the paper's
`U(X^e)` in `ℤ[X] / span {Φ₂₉}`. -/
theorem cyclicToPolynomialQuotient_U (e : Z29) :
    cyclicToPolynomialQuotient (U e) =
      sectionFourU (quotientX ^ e.val) := by
  simp only [U, map_sum, cyclicToPolynomialQuotient_monomial,
    sectionFourU]
  apply Finset.sum_congr rfl
  intro s _
  rw [quotientX_pow_zmod_mul]

/-- Evaluation of the cyclic representative `paperEntry e` is exactly
`A_e(X)`. -/
theorem cyclicToPolynomialQuotient_paperEntry (e : Z29) :
    cyclicToPolynomialQuotient (paperEntry e) = sectionFourAEntry e.val := by
  change cyclicToPolynomialQuotient
      (CyclotomicCertificate.monomial 0 29 - 2 • U e) =
    (29 : PolynomialCyclotomicRing) -
      2 • sectionFourU (quotientX ^ e.val)
  rw [map_sub, map_nsmul, cyclicToPolynomialQuotient_monomial,
    cyclicToPolynomialQuotient_U]
  norm_num

/-- Replacing a natural exponent by its residue does not change `A_e(X)` in
the literal polynomial quotient. -/
theorem sectionFourAEntry_natCast_val (n : ℕ) :
    sectionFourAEntry ((n : Z29).val) = sectionFourAEntry n := by
  unfold sectionFourAEntry
  rw [quotientX_pow_natCast_val]

/-- Evaluation of the literal cyclic matrix gives the literal polynomial
matrix `A(X)` entry by entry. -/
theorem literalCyclotomicMatrix_map_eq_sectionFourMatrix :
    literalCyclotomicMatrix.map cyclicToPolynomialQuotient =
      sectionFourMatrix := by
  ext j k
  change cyclicToPolynomialQuotient
      (paperEntry
        (((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29))) =
    sectionFourAEntry ((j.val + 1) * (k.val + 1))
  have he :
      (((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29)) =
        (((j.val + 1) * (k.val + 1) : ℕ) : Z29) := by
    simp only [Nat.cast_mul]
  rw [he, cyclicToPolynomialQuotient_paperEntry,
    sectionFourAEntry_natCast_val]

/-- Evaluation of the cyclic square-counting polynomial gives exactly
`∑_(a=0)^28 X^(a²)`. -/
theorem cyclicToPolynomialQuotient_gaussSquares :
    cyclicToPolynomialQuotient gaussSquares = sectionFourGauss := by
  rw [gaussSquares_eq_sum_monomial_sq, map_sum]
  simp only [cyclicToPolynomialQuotient_monomial, Int.cast_one,
    one_mul, sectionFourGauss]
  change (∑ a : Z29, quotientX ^ (a ^ 2).val) =
    ∑ a : Z29, quotientX ^ (a.val ^ 2)
  apply Finset.sum_congr rfl
  intro a _
  exact quotientX_pow_zmod_sq a

/-! ## Transport from the cyclic quotient -/

/-- The defining cyclotomic polynomial is zero in its quotient. -/
@[simp]
theorem polynomialQuotientMap_cyclotomic :
    polynomialQuotientMap (Polynomial.cyclotomic 29 ℤ) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton_self (Polynomial.cyclotomic 29 ℤ)

/-- The cyclic sum `1 + X + ⋯ + X²⁸` maps to zero in the literal
polynomial quotient. -/
@[simp]
theorem cyclicToPolynomialQuotient_cyclotomicSum :
    cyclicToPolynomialQuotient cyclotomicSum = 0 := by
  rw [cyclotomicSum, map_sum]
  simp only [cyclicToPolynomialQuotient_monomial, Int.cast_one,
    one_mul]
  change (∑ e : Fin 29, quotientX ^ e.val) = 0
  rw [Fin.sum_univ_eq_sum_range]
  calc
    (∑ e ∈ Finset.range 29, quotientX ^ e) =
        polynomialQuotientMap
          (∑ e ∈ Finset.range 29, X ^ e) := by
      simp only [map_sum, map_pow, quotientX]
    _ = polynomialQuotientMap (Polynomial.cyclotomic 29 ℤ) := by
      congr 1
      rw [Polynomial.cyclotomic_prime]
    _ = 0 := polynomialQuotientMap_cyclotomic

private theorem cyclicIdeal_maps_zero :
    ∀ a : Cyclic ℤ,
      a ∈ Ideal.span ({cyclotomicSum} : Set (Cyclic ℤ)) →
        cyclicToPolynomialQuotient a = 0 := by
  intro a ha
  rcases Ideal.mem_span_singleton'.mp ha with ⟨b, hb⟩
  rw [← hb, map_mul, cyclicToPolynomialQuotient_cyclotomicSum,
    mul_zero]

/-- The natural map from the cyclic presentation of the cyclotomic quotient
to the paper's literal polynomial quotient.  Only this direction is needed
for equation (4.1), so no unnecessary global quotient equivalence is used. -/
def cyclicQuotientToPolynomialQuotient :
    CyclotomicRing →+* PolynomialCyclotomicRing :=
  Ideal.Quotient.lift
    (Ideal.span ({cyclotomicSum} : Set (Cyclic ℤ)))
    cyclicToPolynomialQuotient.toRingHom
    cyclicIdeal_maps_zero

@[simp]
theorem cyclicQuotientToPolynomialQuotient_mk (x : Cyclic ℤ) :
    cyclicQuotientToPolynomialQuotient (cyclotomicQuotientMap x) =
      cyclicToPolynomialQuotient x := by
  rfl

@[simp]
theorem cyclicQuotientToPolynomialQuotient_literalGauss :
    cyclicQuotientToPolynomialQuotient literalQuotientGauss =
      sectionFourGauss := by
  rw [literalQuotientGauss,
    cyclicQuotientToPolynomialQuotient_mk,
    cyclicToPolynomialQuotient_gaussSquares]

@[simp]
theorem literalQuotientMatrix_map_eq_sectionFourMatrix :
    literalQuotientMatrix.map cyclicQuotientToPolynomialQuotient =
      sectionFourMatrix := by
  ext j k
  change cyclicQuotientToPolynomialQuotient
      (cyclotomicQuotientMap
        (paperEntry
          (((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29)))) =
    sectionFourAEntry ((j.val + 1) * (k.val + 1))
  rw [cyclicQuotientToPolynomialQuotient_mk]
  have he :
      (((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29)) =
        (((j.val + 1) * (k.val + 1) : ℕ) : Z29) := by
    simp only [Nat.cast_mul]
  rw [he, cyclicToPolynomialQuotient_paperEntry,
    sectionFourAEntry_natCast_val]

private theorem permanent_map_ringHom
    {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) :
    Matrix.permanent (M.map f) = f (Matrix.permanent M) := by
  classical
  simp only [Matrix.permanent, Matrix.map_apply, map_sum, map_prod]

/-! ## Equation (4.1) -/

/-- **Equation (4.1) in the paper's actual coefficient ring.**  The single
certified integer equality transports from the already proved cyclic
quotient certificate to
`ℤ[X] / span {Polynomial.cyclotomic 29 ℤ}` with all displayed Section 4
objects identified literally. -/
theorem equation_four_one_of_canonicalConstant
    (hcanonical : canonicalConstant = certificateInteger) :
    sectionFourGauss * Matrix.permanent sectionFourMatrix =
      (certificateInteger : PolynomialCyclotomicRing) := by
  calc
    sectionFourGauss * Matrix.permanent sectionFourMatrix =
        cyclicQuotientToPolynomialQuotient literalQuotientGauss *
          cyclicQuotientToPolynomialQuotient
            (Matrix.permanent literalQuotientMatrix) := by
      rw [cyclicQuotientToPolynomialQuotient_literalGauss,
        ← permanent_map_ringHom cyclicQuotientToPolynomialQuotient
          literalQuotientMatrix,
        literalQuotientMatrix_map_eq_sectionFourMatrix]
    _ = cyclicQuotientToPolynomialQuotient
          (literalQuotientGauss *
            Matrix.permanent literalQuotientMatrix) := by
      rw [map_mul]
    _ = cyclicQuotientToPolynomialQuotient
          (certificateInteger : CyclotomicRing) := by
      rw [literal_ring_certificate_of_canonicalConstant hcanonical]
    _ = (certificateInteger : PolynomialCyclotomicRing) := by
      exact map_intCast cyclicQuotientToPolynomialQuotient certificateInteger

/-- Fully expanded numerical form of equation (4.1). -/
theorem equation_four_one
    (hcanonical : canonicalConstant = certificateInteger) :
    (∑ a : Fin 29, quotientX ^ (a.val ^ 2)) *
        Matrix.permanent
          (fun j k : Fin 14 ↦
            (29 : PolynomialCyclotomicRing) -
              2 • sectionFourU
                (quotientX ^
                  ((j.val + 1) * (k.val + 1)))) =
      ((-84_643_985_981_440 * 29 ^ 14 : ℤ) :
        PolynomialCyclotomicRing) := by
  change sectionFourGauss * Matrix.permanent sectionFourMatrix =
    (certificateInteger : PolynomialCyclotomicRing)
  exact equation_four_one_of_canonicalConstant hcanonical

end
end PolynomialQuotientCertificate
end SunCotangent
