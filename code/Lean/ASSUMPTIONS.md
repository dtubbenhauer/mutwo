# Mathematical inputs and computational trust

The Lean project verifies the paper's fixed-source affine KL row sum and
its first-cohomology consequence **conditional on explicit general
literature inputs**. The final theorem is
`Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness`.
The framework theorems supplied as arguments have not themselves been
formalized in this project.

## Mathematical inputs

The final theorem takes three arguments:

| Argument | Mathematical content |
|---|---|
| `Hecke.TheoryFamily` | The affine type-A Coxeter model, the standard and canonical Hecke bases, and ordinary KL positivity. |
| `PolynomialWebLiterature` at each rank | Canonical refinement span and the full-flag orbit/Hecke-convolution realization. |
| `CoordinateLiteratureTransfer.Inputs` | Highest-weight existence, Andersen/AJS, BNP, Steinberg restriction, and PSL simplicity. |

The exact statements, conventions and source qualifications are in
[literature-inputs.md](literature-inputs.md). These are mathematical
hypotheses in theorem types, not new foundational Lean axioms. An axiom
audit does not establish their existence or validate their interpretation.

## What the project proves

The project proves the explicit affine family, the fixed web's ordered and
winding-sensitive evaluation, the six-map identity, flag counts, canonical
correction, and row sum. Polynomial/completed lattice comparisons and the
coordinate-cohomology comparison are proved constructions on the final
theorem's dependency path. The row sum is not assumed.

For `m >= 2`, the row sum is `m*(m+1)/2`; hence at least one coefficient is
at least `floor(m/2)+1`. The named modules satisfy the corresponding
cohomological conclusion for sufficiently large primes, with the
rank-dependent character-formula threshold and the separate bound
`p >= 5*(2*m)`. The individual formula `mu_(j;m) = j` for all parameters and
a fixed-characteristic result are not proved.

The graph verification concerns the manuscript's fixed presentation. It
does not construct a global annular isotopy quotient. See
[graph-evaluation.md](graph-evaluation.md) and [proof-map.md](proof-map.md).

## Computational trust

Project Lean proofs contain no `sorry`, `admit`, new axiom declarations,
`native_decide`, unsafe proof escape or compiled proof oracle. The admitted
foundational dependencies are Lean's `propext`, `Classical.choice` and
`Quot.sound`. Python generates certificates and runs audits; its numerical
output is not a premise of the Lean theorems.

The build pins Lean `v4.22.0-rc2` and mathlib commit
`49af9b7fd7e19db08a946b5bd08d1a5bc39dfd3d`, with transitive dependencies in
`lake-manifest.json`. `python3 scripts/verify.py` builds both targets, checks
the principal theorem axioms and exact interfaces, regenerates certificates,
and runs negative controls for the audit mechanism. Use ordinary Python,
without `-O`, because provenance checks use assertions.

## Manuscript and saved reports

The supplied reports record a prior build. The reviewed manuscript is
identified by its historical hash in
`certificates/manuscript-review.json`; that hash does not identify later
manuscript revisions. The repository's current manuscript is provided
separately. Source hashes identify checked files but do not establish
semantic equivalence between a manuscript and a formal theorem.
