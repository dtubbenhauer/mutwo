# Lean formalization of *Annular webs and Guralnick's conjecture*

This project formalizes the manuscript's route from the explicit affine
family, actual checked web graph and integral six-map construction to
unbounded first-cohomology dimensions,
**conditional on explicit general literature inputs**. The endpoint is
`Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness`; its hypotheses are
`Hecke.TheoryFamily`, a `PolynomialWebLiterature` bundle at each rank, and
`CoordinateLiteratureTransfer.Inputs`. Their contents and source-checking limitations
are listed in [literature-inputs.md](literature-inputs.md).

The original row-sum theorem is a proved intermediate statement, not an
assumed literature input. The same applies to the main/auxiliary gallery
counts, support, auxiliary canonicality, correction, and the application
to the named highest-weight family. The result concerns mathlib's actual
H^1 of actual representations of `PSL_(2m+1)(F_p)`; it is not a theorem
about numerical encodings alone.

The elementary inputs identified in the audit are now proved: finite flag
enumeration, polynomial coordinate formulas, KL inversion and diagram
invariance, parabolic longest elements and all parabolic laws, the matrix
length dictionary, and the full-to-partial convolution normalization.
`PolynomialWebLiterature` retains only two fields: canonical refinement span
and full-flag orbit/Hecke realization. Canonical support is now derived from
refinement; bar involutivity and nontriviality of the family action are also
proved. Andersen's unused H¹ finiteness clause has been removed. See
[audit-input-necessity.md](audit-input-necessity.md),
[audit-elementary-inputs.md](audit-elementary-inputs.md) and
[audit-full-flag-normalization.md](audit-full-flag-normalization.md).

This is **not an unconditional Lean disproof**: the cited framework and
representation-theoretic theorems have not themselves been formalized.
The current verification includes failing guards for the principal axiom
checks, exact endpoint types and the literature interfaces, with only the
standard foundational axioms allowed. Counts and build evidence are in
`reports/verification.json`.
Read [status.md](status.md) for the exact limits, and
[proof-map.md](proof-map.md) for the dependency graph.

The specific graph-evaluation gap found in the earlier audit is now closed.
The ordered, winding-sensitive replay equals the original graph; its full
right Hecke-module morphism equals the six-map composite. See
[graph-evaluation.md](graph-evaluation.md) for the construction and scope.
This concerns the manuscript's fixed presentation, not a global annular
isotopy quotient.

The model comparisons are now explicit proofs: global polynomial/completed
lattice equivalence, preservation of degrees, flags, galleries and coordinate
quotients, and the exact coordinate-ring representation and regular H¹
comparison. The final theorem passes through these conversions. See
[audit-model-comparisons.md](audit-model-comparisons.md) for their scope and
the precise full-flag realization that remains cited input. An
[independent semantic review](audit-model-comparison-review.md) checks the
completed comparisons and the final theorem path. The previous
three assumption reductions are recorded in
[audit-assumption-reduction.md](audit-assumption-reduction.md).

The primary-source audits of the [affine framework](audit-primary-affine.md)
and [cohomological transfer](audit-primary-transfer.md), with the
[Andersen follow-up](audit-andersen-followup.md), distinguish checked
citations from source-access qualifications and the model comparisons
that have now been proved.

## Statement

For each `m>=2`, the ordinary affine KL coefficients with prescribed lower
endpoint `w0` satisfy `sum_(j=1)^m mu_(j;m)=choose(m+1,2)`. For every
sufficiently large prime (with a rank-dependent AJS threshold and the
separate bound `p>=5(2m)`), the paper's named modules are finite-dimensional,
faithful and absolutely irreducible, and have these H^1 dimensions.
Consequently some member has dimension at least `floor(m/2)+1`.

Thus there is no single bound valid for all fields, finite groups and
faithful finite-dimensional absolutely irreducible modules. The proof
already supplies examples over algebraic closures of prime fields and
finite simple projective special linear groups. It does not establish the
conjectural individual formula `mu_(j;m)=j` or a fixed-characteristic result.

## Reproducible build

Pinned versions:

- Lean `leanprover/lean4:v4.22.0-rc2`, commit
  `6a60de2ac701d1a3f5dc88894b7822f17c3a980b`.
- mathlib `49af9b7fd7e19db08a946b5bd08d1a5bc39dfd3d`.
- Transitive dependencies locked in `lake-manifest.json`.

From this `code/Lean/` directory, with Elan and Python 3 installed:

```sh
elan toolchain install leanprover/lean4:v4.22.0-rc2
lake exe cache get
lake build
python3 scripts/verify.py
```

`lake exe cache get` is optional if matching dependencies are already built.
It fetches mathlib artifacts, not proofs of this project's theorems. There
are no absolute dependency paths or symlinked packages in the build
configuration. `.lake/` is disposable.

`lake build` requires both `Guralnick` (the mathematical library) and
`GuralnickAudit` (diagnostic and failing regression checks). To build only
the library, use `lake build Guralnick`. The standalone audit is
`lake build GuralnickAudit`; run `lake env lean Guralnick/AxiomAudit.lean`
to print the diagnostic report directly.

`verify.py` checks coverage across the two targets, the pins, proof escapes,
the reviewed manuscript hashes, certificate regeneration, both builds and
principal theorem axioms. It also runs negative controls which must reject
a wrong axiom expectation and an additional unavailable theorem premise.
The portable release/CI entrypoint is `sh scripts/ci.sh`. This does not
configure hosted CI or publish a source revision.
It writes `reports/lake-build.txt`, `reports/axioms.txt` and
`reports/verification.json`. Mathematical assumptions passed as theorem
arguments are printed separately from foundational axiom dependencies.

`GuardedAudit.lean` locks the explicit final arguments `T`, `W`, `I`, the
named-family conclusion and its characteristic bounds. It also guards
interface definitions, so adding a hypothesis inside a literature bundle
cannot silently evade the endpoint check. These checks detect source
drift; they do not prove the cited statements or their interpretation.
Content hashes in the release report identify the exact checked sources.

## Navigation

- [WebGraphProof.lean](Guralnick/WebGraphProof.lean): complete graph-morphism
  identification and corrected graph coefficient.
- [WebProof.lean](Guralnick/WebProof.lean): final row theorem and named-module
  counterexample, with only the literature bundles as hypotheses.
- [ModelComparisonCounterexample.lean](Guralnick/ModelComparisonCounterexample.lean):
  the row theorem, same named module family and final counterexample with
  both proved model conversions on the proof path.
- [PolynomialWebLiterature.lean](Guralnick/PolynomialWebLiterature.lean) and
  [CoordinateLiteratureTransfer.lean](Guralnick/CoordinateLiteratureTransfer.lean):
  final literature interfaces and proved conversions to the earlier models.
- [proof-map.md](proof-map.md): objects, conventions, original lemmas and
  dependency graph.
- [audit-updated-manuscript.md](audit-updated-manuscript.md): comparison with
  the 2 November manuscript and decisions on all five recommendations.
- [audit-framework-inputs.md](audit-framework-inputs.md) and
  [audit-updated-transfer.md](audit-updated-transfer.md): exact input fields,
  sources and convention conversions.
- [audit-seed-coverage.md](audit-seed-coverage.md): the completed seed web
  correction, exact canonical decomposition and actual individual KL polynomials.
- [literature-inputs.md](literature-inputs.md): source ledger, including the
  general inputs stated in the original polynomial and coordinate-ring models.
- [graph-evaluation.md](graph-evaluation.md): the proved graph-to-map bridge,
  winding safeguards, local relations and fixed-presentation scope.
- [audit-fidelity.md](audit-fidelity.md): follow-up adversarial comparison
  with the manuscript, new kernel-checked fidelity lemmas and independent
  finite experiments; its former graphical gap is resolved by the new bridge.
- [formalization-review.md](formalization-review.md): semantic fidelity and
  what is outside the formalization.
- [gaps.md](gaps.md): critical findings and possible improvements. No
  definite manuscript gap has been established; the earlier integral
  presentation concern was resolved by the paper's direct module maps.
- [audit-affine-interfaces.md](audit-affine-interfaces.md) and
  [audit-final-interfaces.md](audit-final-interfaces.md): independent checks
  of the general interfaces and fixed-source transfer.

`audit-web.md` and `audit-transfer.md` preserve the earlier mathematical
source audits. Their historical descriptions of formalization progress
are superseded by `status.md` and the present sources.

## Certificates and comparisons

```sh
python3 scripts/generate_windows.py
lake build Guralnick.WindowExamples
python3 scripts/compare_kl.py
python3 scripts/audit_arithmetic.py
python3 scripts/audit_finite_gallery_fidelity.py
python3 scripts/audit_web_interfaces.py
```

Fourteen window certificates (`2<=m<=5`, every `1<=j<=m`) are checked by
Lean against the actual sorted family, permutation inverse, zero winding
sum, matrix entries, inversion count and inverse-dot weights. The checker
soundness theorem constructs an actual affine permutation. An invalid
certificate is rejected. Uniform family, matrix and length results are
proved separately; finite cases are not used for extrapolation.

The finite certificate primes verify coordinate inequalities, not the
AJS character-formula threshold. Python is an untrusted generator.
`compare_kl.py` and `audit_arithmetic.py` are explicitly experimental
independent comparisons, as are the two fidelity-audit scripts. Run them
without `-O`, since they use assertions.
`SeedPolynomials.lean` now proves both actual seed KL polynomials, `1+X`
and `1+4X+5X²+4X³+2X⁴`. The proof follows the paper: full rank-one standard
expansion and canonical correction, exact five-term canonical decomposition,
actual web-coordinate readout, and KL normalization. It uses the same
general literature inputs and adds no seed premise. This is a kernel-checked
web calculation, not an independent implementation of KL recursion. The
uniform row proof does not depend on the seed example.

## Proof integrity and provenance

There is no `sorry`, `admit`, newly declared axiom, `native_decide`, unsafe
proof escape or compiled proof oracle in project Lean sources. Kernel
proofs may use the standard foundations `propext`, `Classical.choice` and
`Quot.sound`. The extensive literature assumptions are explicit theorem
parameters; the axiom audit alone does not validate their mathematical
interpretation.

The manuscript recorded by the supplied audit is `PolishedWebProof/main.tex`, reviewed
2 November 2026, SHA-256
`1f926a87b4000953c4c32b0995c844687ab68861100a9ce39b07a965308ca8a4`.
Its figures are embedded TikZ. `certificates/manuscript-review.json` records
this file, the previous `main_old.tex` and the uploaded recommendations.
The earlier source inventory is retained as historical provenance, not
silently overwritten with the new paper. No applicable `AGENTS.md` was
found. The manuscript and recommendations were not edited.

Supporting programs/data were located in `RevisedWeb/code/` and
`RevisedWeb/data/`. Unchanged reference copies and provenance hashes are in
`certificates/source-inventory.json`. The updated verification remark is
compared with the actual scope in `audit-updated-manuscript.md`.

## Standalone package

This copy includes the current Lean sources, pinned configuration, audit
scripts, required certificate data and assumption/fidelity ledgers. The
proof and build-configuration files are byte-identical to the reviewed
research project; the README adds these packaging instructions.

The current repository includes a later manuscript in
[paper/main.tex](../../paper/main.tex), with its compiled PDF and separate
figure exports. That source is unchanged from the latest upload. It is not
the earlier manuscript identified in `certificates/manuscript-review.json`;
the earlier source and uploaded feedback were not supplied. Their reviewed
hashes remain unchanged, and the verifier records those historical inputs
as absent in this standalone layout. The original complete-project report
is retained as `reports/original-verification.json`; `reports/verification.json`
records the earlier code-package check. No fresh Lean compilation was run
when preparing this GitHub layout. All 249 Lean source files and the pinned
configuration are unchanged. No path to the research workspace is needed
to build this project. Dependency downloads/build caches are not included.

The supplementary exact Python computations are in
`../finite_computations/`. They are not premises of the Lean theorems.
Optional Python comparison scripts in this Lean folder are also
experimental, not proof oracles.
