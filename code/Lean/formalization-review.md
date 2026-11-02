# Semantic fidelity review

Updated 30 October 2026. This review concerns what the definitions mean;
`#print axioms` alone cannot establish semantic fidelity.

- The affine group consists of a residue permutation and zero-sum winding
  vector, with the actual periodic action on integers. `Family.affine` is
  proved equal to the sorted input window; `Family.upper` is its actual
  product with the finite longest permutation. Length and descents use an
  explicit general affine Coxeter identification, not the proposed gap as
  a definition of length. The family gap is independently proved.
- The Hecke algebra is presented by actual braid and quadratic relations.
  Standard and canonical bases satisfy generic KL axioms as explicit
  literature hypotheses. Ordinary polynomials are linked to those bases
  by their precise normalization. The family coefficients are extracted
  from those polynomials. No definition assigns them the values `j` or
  the claimed row sum.
- The main web has graph, edge thickness, vertex types, boundary order,
  local ribbon orders and seam-winding data. Its boundary cuts are proved
  equal to the concrete parabolic masks. The algebraic proof uses the
  manuscript's direct integral inclusion/merge maps. A complete quotient
  annular web category and an evaluation theorem for every diagram are
  outside this formalization; this is a framework interpretation, not an
  original coefficient lemma being silently assumed.
- The raw element is a composite of those maps, not a quotient introduced
  by division. Its cleared numerator identity is proved. Ordinary
  positivity applies to that numerator; no invalid claim of positivity
  after division is used. A Lean counterexample records why that inference
  would be false in general.
- Flags are actual finitely generated full power-series lattices in a
  Laurent-series vector space. Gallery choices, quotient subspaces and
  relative positions are genuine mathematical data. The six-map and
  auxiliary gallery bijections, support restrictions and finite counts
  are proved. General lattice theory and the complete polynomial/completed
  flag/gallery comparison are now proved. The remaining general polynomial
  orbit-coordinate and normalized convolution formulas remain cited input.
- Canonicality of auxiliary words is obtained from their standard
  coordinates, bar symmetry and triangular degree bounds. It is not a
  field of the literature structure. Reflections act on actual affine
  windows and matrices. Canonical multiplicity allowances are established
  uniformly before critical-degree readout.
- Gaussian polynomials use their recursion and signed out-of-range
  convention. Their cancellation identities are proved uniformly, not
  inferred from sampled cases. The original four-case counts are not
  hidden inside the definition of the raw element.
- Rational cohomology is defined by regular cochains of actual polynomial
  representations; finite-group H^1 uses mathlib's group cohomology. Its
  coordinate-Hopf-algebra representation and regular tensor-complex
  comparisons are proved. The theorem identifying this complex with derived
  rational cohomology remains the cited Jantzen input.
  The module family is selected by its actual highest weight, then
  restricted and descended to the actual central quotient. A separate
  theorem relates its H^1 dimension to the actual fixed-source KL value.
- Finite-dimensionality is included or proved where `finrank` is used, so
  default zero finrank for infinite-dimensional spaces cannot certify an
  intended dimension. Absolute irreducibility is a scalar-extension
  predicate, and faithfulness is injectivity of the representation map.

The external framework is extensive. Its interfaces must be checked
mathematically against the cited theorems, independently of the kernel
checking the implication from them. `literature-inputs.md` and the
independent interface audits identify these boundaries. A successful build
is a proof of the stated conditional theorem, not a formal proof that all
of its literature inputs exist.

The full seed KL polynomial supplied by the research computations is not
independently certified as a KL polynomial by this project. Kernel checks
of its Laurent reversal are labeled accordingly. It is not used to infer
the uniform row theorem. The individual rule `mu_(j;m)=j` remains separate
from the manuscript's proved row-sum target.

## Follow-up adversarial audit (30 October 2026)

The new reports `audit-fidelity-original.md`, `audit-fidelity-web.md` and
`audit-fidelity-transfer.md` compare the actual Lean definitions with the
TeX and inspect the general interfaces for mismatches and vacuity. They
record checks independently of the earlier positive reviews.

That audit found a precise coverage gap: the graph was not connected to
the algebraic word by an evaluation theorem. The subsequent work closes it
for the manuscript's concrete checked presentation. Full ordered replay,
individual windings, all local boundary indices and the integral local maps
now lead to `WebTraceEvaluation.family_graph_evaluation_eq_raw` and the
stronger `WebProof.graph_morphism_eq_sixMaps`. Every standard/canonical
coordinate, and the corrected graph readout, is connected by proved equality.
`WebProof` now imports this bridge. See `graph-evaluation.md` and the
independent `audit-graph-evaluation.md` review.

The evaluation remains attached to the specified presentation. Independence
under arbitrary annular isotopy, the entire SSW category and the full
individual seed KL calculation remain outside the formalized conclusion.

`FidelityKL` proves uniqueness of the standard basis, bar, canonical basis
and ordinary polynomials for a fixed actual Coxeter model satisfying the
KL interface. Thus the polynomial field in that interface cannot be freely
assigned a convenient alternative answer. This is a rigidity theorem, not
a consistency proof for all the separate external framework inputs.

`FidelityWeights` directly compares both the actual module's integral
weight vector and its Dynkin labels with the primary fundamental-weight
formula in the paper, including a rational-coordinate identification of
the fundamental weights. These checks augment
the existing inverse-dot and coordinate proofs. The two new Python audit
scripts count actual finite flags and exhaust bounded small affine windows;
their reports are explicitly experimental, not Lean certificates.


The latest source-level reduction is recorded in
[audit-assumption-reduction.md](audit-assumption-reduction.md): the actual
parabolic scalar's nonvanishing and bar invariance, and the actual
one-period lattice lift, are now proved and removed from the input records.
No original target or construction changed. The accompanying primary-source
reviews, `audit-primary-affine.md` and `audit-primary-transfer.md`, distinguish
source theorems from the then-outstanding completion/flag and rational-function
comparisons. Those explicit model comparisons are now proved; see
`audit-model-comparisons.md` and `audit-rational-coordinate-comparison.md`. Andersen's original full-text convention check remains open.


The subsequent lattice verification constructs `LaurentLattice.provedTheory`
from the actual power-series modules. `GeneralLatticeFlagInput` no longer
assumes these four general facts. The finite natural completion equivalence
and bounded actual-lattice correspondence are also proved. The complete
polynomial/completed affine flag comparison has since been assembled in
`PolynomialFlags` and transferred through arbitrary Laurent coordinate
changes. `ModelComparisonCounterexample` uses these proved conversions and
the coordinate-H1 equivalence on the path to the same original family and
final counterexample statement. The normalized polynomial convolution
theorem itself remains source-derived cited input, as recorded in
[literature-inputs.md](literature-inputs.md).
