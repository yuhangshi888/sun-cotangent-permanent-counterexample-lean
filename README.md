# A Lean formalization of a counterexample to Sun's sign conjecture

[![CI](https://github.com/yuhangshi888/sun-cotangent-permanent-counterexample-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/yuhangshi888/sun-cotangent-permanent-counterexample-lean/actions/workflows/ci.yml)

Yuhang Shi<br>
Email: yuhangshi888@gmail.com<br>
Formalization version 1.0.1 — August 27, 2026. Not peer reviewed.

This repository proves in Lean 4 the exact identity

\[
\sqrt{29}\,\operatorname{per}
  \left[\cot\!\left(\frac{\pi jk}{29}\right)\right]_{1\le j,k\le14}
=84\,643\,985\,981\,440.
\]

Because the Legendre symbol \(\left(\frac{-1}{29}\right)=1\), the
displayed positive value reverses the cotangent inequality in Zhi-Wei Sun's
Conjecture 4.7(ii). The result does not address Conjecture 4.7(i), the other
inequality in part (ii), or Sun's distinct sine and cosecant permanent
conjectures.

- Paper source, fixed release: [v1.0.0](https://github.com/yuhangshi888/sun-cotangent-permanent-counterexample/tree/v1.0.0), commit `1d5d637547cda37b4122b905e910afa739cdb90a`
- Archived preprint: [Zenodo DOI 10.5281/zenodo.22105063](https://doi.org/10.5281/zenodo.22105063)
- Mathematical background: [Zhi-Wei Sun, arXiv:2108.07723v7](https://arxiv.org/abs/2108.07723v7)

## Proof architecture

The Comparator-facing proof uses a three-modulus integral cyclotomic
certificate. Two new 61-bit residue moduli and the middle modulus from the
paper are specialized at explicit twenty-ninth roots. One kernel-checked Gray
scan, split into 128 checkpoint segments with 129 boundary accumulators,
computes the three packed permanents.
Before these scalar evaluations are used, invariance of the certificate under
`X ↦ X²` and the fact that `2` generates the nonzero residues modulo `29`
show that all 28 nonzero cyclic coefficients are equal. Subtracting their
common multiple of the cyclotomic sum therefore leaves a quotient normal form
with a single canonical constant. Each scalar specialization determines this
one constant modulo its modulus; the resulting statements about all 28
canonical positions follow from the normal form rather than from 28 separate
permanent evaluations. Pairwise coprimality and an explicit product bound then
lift the coefficients to integers. This proves equation (4.1), and the
formalized Gauss-sum and cotangent bridge gives the exact real identity above.

The repository also contains a six-small-modulus certificate that is
independent of the preceding residue computation. Its own compact scan has
128 checkpoint segments and determines the same canonical constant.
It supplies the three literal rows of Table 1, the finite-field residues and
CRT reconstruction from Section 3, and an independent route to the same exact
value. Neither finite computation is assumed as an axiom.

## Paper coverage

| Paper component | Lean coverage |
|---|---|
| Permanent convention | The paper's row-first permutation sum is proved equal to `Matrix.permanent` |
| Quadratic Gauss sum | Primitive root, character sum, square evaluation, positivity, and `G = sqrt 29` |
| Cotangent reduction | Nonzero denominators, `cot = i R`, `i^14 = -1`, and the permanent scaling |
| The polynomial `U` | The telescoping identity, complex inverse identity, finite-ring inverse identity, and entry specialization |
| Table 1 | All three primes, displayed roots, root orders, nonzero denominators, Gauss sums and their squares, permanents, and final residues |
| Ryser and Glynn formulas | Both generic formulas are proved equal to the permutation-sum permanent |
| Section 3 CRT | The displayed `N` and `M`, centered representative, congruences, and uniqueness argument |
| Archimedean estimate | Cotangent bounds, permanent bound, `sqrt 29 < 6`, four displayed decimal expansions, and both strict comparisons |
| Equation (4.1) | Both the cyclic group-ring form and the literal quotient `Z[X]/(Phi_29)` form |
| Cyclotomic normal form | Invariance under `X ↦ X²`, equality of the nonzero cyclic coefficients, and reduction to one canonical constant |
| Section 4 lifting | Submultiplicative `l1` bounds, `B = 14! * 29^29`, all 28 coefficient bounds, three-modulus product, and integer lifting |
| Analytic return | Quadratic-residue square count, Gauss specialization, matrix specialization, cancellation, exact value, and sign consequence |

The main files are:

- `SunCotangent/AdvertisedTheorem.lean` — the exact value and sign theorem used by `Solution.lean`;
- `SunCotangent/ThreeScalarCyclotomicCertificate.lean` — the three-61-bit-modulus certificate, independent of the six-small-modulus computation, and coefficient lifting;
- `SunCotangent/GrayPermanentCheckpointsCompact.lean` — the six-small-modulus checkpoint certificate;
- `SunCotangent/MainTheorem.lean` — both unconditional routes and the paper-level Section 3 and Section 4 statements;
- `SunCotangent/PaperPermanentConvention.lean` — the paper/Mathlib permanent convention and formula agreement;
- `Challenge.lean`, `Solution.lean`, and `comparator.json` — the small Palomar statement surface and matching proofs.

## Fidelity boundaries

The exact value and sign counterexample are unconditional. The following
implementation boundaries are kept explicit:

- The paper cites Sun's general integrality theorem for all odd primes. This
  repository proves integrality at `p = 29` from the unconditional exact value;
  the separately exposed Section 3 reconstruction keeps general integrality
  as an explicit literature hypothesis and is not used by the advertised
  proof.
- Membership in `Z[zeta, 1/29]` is represented by the exact inverse and
  specialization identities actually needed in the proof, rather than by a
  separately constructed localization object.
- Ryser's and Glynn's formulas are both proved correct. The numerical
  checkpoint certificates use the Gray/Ryser recurrence; no second numerical
  Glynn checkpoint trace is claimed.
- The paper's original first and third 61-bit extension-valued C++ scans are
  not replayed instruction by instruction. Their stated moduli, product,
  bounds, and coefficient congruence conclusions are formalized, while the
  independent Lean three-scalar route uses two new moduli plus the paper's
  middle modulus. It proves the same integral equation without depending on
  the six-small-modulus route.

These are fidelity distinctions between implementations, not hypotheses of
the advertised theorem.

## Trust and Palomar statement surface

The substantive development under `SunCotangent/` and `Solution.lean`
contains no `sorry`; it declares no custom axiom and uses neither
`native_decide` nor `Lean.ofReduceBool`. `Challenge.lean` contains exactly two
deliberate statement placeholders, a structure allowed by Comparator; they
are not dependencies of `Solution.lean` and are excluded from the substantive
`sorry_count`.

Comparator checks these declarations:

- `SunCotangentP29.cotangentPermanent29_exact`
- `SunCotangentP29.sunSignCounterexample`

The permitted axiom boundary is the standard Palomar set `propext`,
`Quot.sound`, and `Classical.choice`. The release procedure additionally
exports and independently replays the selected proofs with NanoDa.

## Verification

The repository pins Lean 4.32.0 and Mathlib v4.32.0. From the repository root:

```text
lake exe cache get
lake build SunCotangent Challenge Solution
lake env lean -DwarningAsError=true SunCotangent/MainTheorem.lean
(cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update)
(cd docbuild && lake build SunCotangent:docs)
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

Run the `docbuild` update command only after changing dependencies; ordinary
verification can use the committed manifests directly. The final command
requires Linux, Git, Go, Ruby, Rust/Cargo, Python 3, and a working Landrun
sandbox. CI runs the complete build, documentation build, and pinned
Comparator/NanoDa toolchain against the checked-out commit.

Palomar submissions use the current [submission service](https://submit.palomar-registry.org/).
Mechanical acceptance records compilation, statement equality, and the axiom
boundary; it is not mathematical peer review or a novelty judgment.

## Authorship, automation, and licence

Yuhang Shi is the formalization author and responsible maintainer. OpenAI
Codex assisted with proof development, exact certificate construction,
compilation, and adversarial checking. Responsibility for the mathematical
claims and the submitted snapshot remains with the author.

The Lean source is licensed under Apache-2.0. The associated preprint is
distributed separately under CC BY 4.0.
