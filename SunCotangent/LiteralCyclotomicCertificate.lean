import SunCotangent.CyclotomicCertificate

/-!
# The literal cyclotomic certificate from Section 4

The computational core uses centered representatives because their exact
`X \mapsto X^2` symmetry reduces the quotient certificate to one integer.
This module proves that those representatives are the same as the literal
polynomials in equation (4.1) after quotienting by
`1 + X + ... + X^28`.

No finite permanent computation is performed here.  The final theorem assumes
only the integer equality `canonicalConstant = certificateInteger` supplied by
the modular certificate.
-/

open scoped BigOperators

namespace SunCotangent
namespace CyclotomicCertificate

noncomputable section

local instance primeFact29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-! ## Literal and centered representatives -/

/-- For a nonzero exponent, the paper's representative
`29 - 2 U(X^e)` is the antisymmetric representative used by the Lean
certificate minus exactly `27 * (1 + X + ... + X^28)`.

The nonzero hypothesis is essential: multiplication by `e` must permute all
twenty-nine cyclic exponents. -/
theorem paperEntry_eq_entry_sub_cyclotomicSum :
    ∀ e : Z29, e ≠ 0 →
      paperEntry e = entry e - (27 : ℤ) • cyclotomicSum := by
  intro e he
  ext x
  simp only [paperEntry, entry, U, cyclotomicSum, monomial,
    AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_smul_apply, Finsupp.sub_apply,
    Finset.sum_apply', AddMonoidAlgebra.single, Finsupp.single_apply]
  revert e x
  decide +kernel

/-- The square-counting definition of `gaussSquares` is coefficientwise the
literal polynomial `sum_(a mod 29) X^(a^2)` used in equation (4.1). -/
theorem gaussSquares_eq_sum_monomial_sq :
    gaussSquares = ∑ a : Z29, monomial (a ^ 2) 1 := by
  ext e
  rw [gaussSquares_coeff]
  unfold squareCount29
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Int.natCast_one, Finset.sum_filter,
    AddMonoidAlgebra.coeff_sum, Finset.sum_apply', monomial,
    AddMonoidAlgebra.single, Finsupp.single_apply]

/-! ## The literal objects in the cyclotomic quotient -/

/-- The quotient map from the cyclic group ring to
`Z[C_29] / (1 + X + ... + X^28)`. -/
def cyclotomicQuotientMap : Cyclic ℤ →+* CyclotomicRing :=
  Ideal.Quotient.mk (Ideal.span ({cyclotomicSum} : Set (Cyclic ℤ)))

@[simp]
theorem cyclotomicQuotientMap_cyclotomicSum :
    cyclotomicQuotientMap cyclotomicSum = 0 := by
  change Ideal.Quotient.mk
      (Ideal.span ({cyclotomicSum} : Set (Cyclic ℤ))) cyclotomicSum = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self cyclotomicSum

/-- The literal `14 x 14` matrix `A(X)` from Section 4, before quotienting. -/
def literalCyclotomicMatrix : Matrix (Fin 14) (Fin 14) (Cyclic ℤ) :=
  fun j k ↦ paperEntry
    (((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29))

/-- Every exponent occurring in the literal matrix is nonzero modulo `29`. -/
theorem literalMatrix_exponent_ne_zero (j k : Fin 14) :
    (((j.val + 1 : ℕ) : Z29) * ((k.val + 1 : ℕ) : Z29)) ≠ 0 := by
  revert j k
  decide +kernel

/-- The literal matrix as an actual matrix over `CyclotomicRing`. -/
def literalQuotientMatrix : Matrix (Fin 14) (Fin 14) CyclotomicRing :=
  literalCyclotomicMatrix.map cyclotomicQuotientMap

/-- The literal quadratic-residue-counting Gauss polynomial in the quotient. -/
def literalQuotientGauss : CyclotomicRing :=
  cyclotomicQuotientMap gaussSquares

/-- The literal left-hand side of equation (4.1), formed inside the quotient. -/
def literalQuotientCertificate : CyclotomicRing :=
  literalQuotientGauss * Matrix.permanent literalQuotientMatrix

theorem cyclotomicQuotientMap_paperEntry (e : Z29) (he : e ≠ 0) :
    cyclotomicQuotientMap (paperEntry e) =
      cyclotomicQuotientMap (entry e) := by
  rw [paperEntry_eq_entry_sub_cyclotomicSum e he, map_sub, map_zsmul,
    cyclotomicQuotientMap_cyclotomicSum]
  simp

theorem cyclotomicQuotientMap_gaussSquares :
    cyclotomicQuotientMap gaussSquares =
      cyclotomicQuotientMap gaussChar := by
  rw [gaussSquares_eq_gaussChar_add_cyclotomicSum, map_add,
    cyclotomicQuotientMap_cyclotomicSum, add_zero]

/-- The paper's matrix and the centered matrix are entrywise equal in the
cyclotomic quotient. -/
theorem literalQuotientMatrix_eq_centered :
    literalQuotientMatrix =
      cyclotomicMatrix.map cyclotomicQuotientMap := by
  ext j k
  exact cyclotomicQuotientMap_paperEntry _
    (literalMatrix_exponent_ne_zero j k)

private theorem permanent_map_ringHom
    {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) :
    Matrix.permanent (M.map f) = f (Matrix.permanent M) := by
  classical
  simp only [Matrix.permanent, Matrix.map_apply, map_sum, map_prod]

/-- The literal quotient certificate is exactly the centered certificate
already used by the modular computation. -/
theorem literalQuotientCertificate_eq_centered :
    literalQuotientCertificate =
      cyclotomicQuotientMap certificatePolynomial := by
  rw [literalQuotientCertificate, literalQuotientGauss,
    cyclotomicQuotientMap_gaussSquares,
    literalQuotientMatrix_eq_centered,
    permanent_map_ringHom]
  exact (map_mul cyclotomicQuotientMap gaussChar
    (Matrix.permanent cyclotomicMatrix)).symm

/-- The centered normal form gives a constant in the quotient as soon as its
single canonical integer has the certified value. -/
theorem centeredQuotientCertificate_of_canonicalConstant
    (hcanonical : canonicalConstant = certificateInteger) :
    cyclotomicQuotientMap certificatePolynomial =
      (certificateInteger : CyclotomicRing) := by
  rw [certificatePolynomial_normalForm, map_add, map_zsmul,
    cyclotomicQuotientMap_cyclotomicSum, hcanonical]
  simp only [zsmul_zero, add_zero]
  change cyclotomicQuotientMap (certificateInteger : Cyclic ℤ) =
    (certificateInteger : CyclotomicRing)
  exact map_intCast cyclotomicQuotientMap certificateInteger

/-- **Literal equation (4.1).**  The one integral equality discharged by the
modular computation implies the paper's coefficientwise identity in the
cyclotomic quotient. -/
theorem literal_ring_certificate_of_canonicalConstant
    (hcanonical : canonicalConstant = certificateInteger) :
    literalQuotientGauss * Matrix.permanent literalQuotientMatrix =
      (certificateInteger : CyclotomicRing) := by
  change literalQuotientCertificate = (certificateInteger : CyclotomicRing)
  exact literalQuotientCertificate_eq_centered.trans
    (centeredQuotientCertificate_of_canonicalConstant hcanonical)

/-!
`PolynomialQuotientCertificate` maps this cyclic presentation directly into
the paper's literal ring `ℤ[X] / (Φ₂₉)`, identifies every displayed
polynomial, and transports the certificate.  A global equivalence of the two
presentations is unnecessary for that exact equation.
-/

end
end CyclotomicCertificate
end SunCotangent
