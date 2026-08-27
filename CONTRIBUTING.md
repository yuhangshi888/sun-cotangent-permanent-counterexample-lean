# Contributing

Corrections and reproducibility improvements are welcome. Please open an
issue before a substantial change and identify the exact declaration, paper
equation, or verification boundary involved.

Pull requests should preserve the literal normalization of the advertised
`p = 29` statements and must not weaken theorem hypotheses, replace
kernel-checked proofs with untrusted computation, or introduce `sorry`, custom
axioms, `native_decide`, or `Lean.ofReduceBool` into the substantive proof.
Keep unrelated refactoring out of mathematical corrections.

Before requesting review, run:

```text
lake build
lake env lean -DwarningAsError=true SunCotangent/MainTheorem.lean
(cd docbuild && lake build SunCotangent:docs)
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

If a change affects the paper correspondence, also update the coverage and
fidelity statements in `README.md` and `formalization.yaml`. No contribution
is represented as peer review or as independently verified until that review
has actually occurred.
