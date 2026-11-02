# Adversarial fidelity audit: web, Hecke and lattice layer

**Follow-up:** the specific graph-evaluation gap recorded below was subsequently
closed for the manuscript's fixed checked presentation. See
[graph-evaluation.md](graph-evaluation.md) for the new proofs and exact scope.
The remainder of this report records the earlier audit state; current build
and completion status are in [status.md](status.md).

30 October 2026. This is a fresh review of actual definitions against
`../main.tex`, not an inference from the successful build or previous audits.
I looked especially for contradictory generic hypotheses, changed
orientations, wrong normalizations, and objects defined by desired outputs.

## Findings

No definite false or inconsistent web-framework hypothesis was found in the
inspected interfaces. The algebraic six-map construction matches the
manuscript. The main remaining distinction is between the proved algebraic
argument and a literal evaluation theorem for the drawn ribbon graph.
The latter is not present and must not be inferred from matched boundaries.

### 1. The orientation difference is intentional

The manuscript's `eq:integral-marked-web` and `eq:marked-symmetrizer`
(`main.tex:3795` and `main.tex:3940`) first construct the integral image
`C_V C_K C_J C_W0 / (h_V h_L^2)`, then apply the inverse-permutation
anti-involution to write a right spherical-module word. Lean's
`ParabolicWeb.Family.raw` uses precisely the former construction, via actual
inclusions and merges. `SphericalMaps.SixMaps.source_cleared_identity` and
`CanonicalChains.main_raw_eq_chain` prove the undivided identity and the
connection to the general chain construction.

The ordinary target is the actual window `u*w0`, and
`Hecke.familyMu_inverse_canonical` explicitly uses simultaneous inversion
for the cohomological index `w0*u^-1`. This does not silently swap the
prescribed lower endpoint for the identity.

### 2. The generic convolution quantifiers survived elementary tests

`FlagConvolution.Input` (`Guralnick/FlagConvolution.lean:52`) ranges over
all chains and all affine indices, including nonmaximal indices. This
could have been dangerously overstrong. Its nil-chain normalization is
consistent: `Chain.raw (.nil I)=C_I`, the gallery is equality of flags,
and for `w` in the finite parabolic the formula gives the standard
coefficient `v^(ell(w_I)-ell(w))`.

For a finite rank-one parabolic, the roundtrip through the empty parabolic
has raw element `C_s^2=(v+v^-1)C_s`. There are `Q+1` intermediate flags.
At `Q=p^2`, `v=1/p`, the exponents in the actual interface give
`v^2(Q+1)=v^2+1` at the identity and `v(Q+1)=v+v^-1` at `s`.
Thus neither omitting maximality in this interface nor the exponent's
use of `length(w)` is by itself an error.

The generic framework still includes the polynomial/completed-lattice
comparison and cyclic-facet extension, as documented in the literature
ledger. The manuscript itself uses `F_Q[[t]]`-lattices in `F_Q((t))^N`
(`main.tex:4073` onward), so the Lean completed-lattice definition matches
the manuscript's model.

I rechecked the source convention in
[Cui, §7.1 and Lemmas 7.1–7.2](https://arxiv.org/html/1407.4557v3): the
convolution identification, target/source order, and subtraction of the
source-parabolic longest length support the formal interface. The parameter
conversion from Cui's `t` is `t=v^-1`. His displayed polynomial-lattice
model does not itself constitute a Lean proof of the completed comparison.

### 3. The actual matrix dictionary has independent stress tests

`OrbitMatrix.ThreeColumnLengthInput` in `Guralnick/OrbitLengthInput.lean`
asserts the dimension/length formula, its maximality converse, and
injectivity on maximal representatives. The inputs are literal inverse
window counts in positive row blocks, not matrices assigned a coefficient.

The new independent program exhausts every balanced shift vector in
`{-1,0,1}^N`, sorts and reverses its translated entries to obtain every
bounded-support right-finite-maximal window, and then checks **every**
positive zero-cut row composition. It tests both directions of the
maximality criterion, the dimension/length equality and uniqueness of
maximal matrix labels, using independently calculated inverse windows and
the finite periodic sum.

| N | Windows | Compositions | Window/composition checks |
|---|---:|---:|---:|
| 3 | 7 | 4 | 28 |
| 4 | 19 | 8 | 152 |
| 5 | 51 | 16 | 816 |
| 6 | 141 | 32 | 4,512 |
| 7 | 393 | 64 | 25,152 |

All 30,660 checks passed. This tests the broad hypothesis on many matrices
outside the manuscript's family; it is not a proof of that external theorem.

### 4. The Gaussian flag inputs include the needed boundary guards

`GalleryCounting.FiniteFlagCounts` (`Guralnick/GalleryCounting.lean:60`)
has a positive ambient-dimension guard for hyperplanes. Its intermediate
and adjacent flags use signed Gaussian lower indices, so dimensions below
the lower subspace and above the upper subspace give zero. No false
zero-dimensional hyperplane formula was found.

Independent enumeration of **all actual vector subspaces** of `F_2^d`,
for `0<=d<=4`, checks the hyperplane, intermediate-subspace and adjacent-flag
formulas for all nested intervals and dimensions through `d+2`. All 8,214
formulas passed, including invalid dimensions. This is separate from the
paper's original four-case gallery formula, which Lean derives from those
general counts and an actual configuration equivalence.

### 5. Graph faithfulness has a precise boundary

`Web.family` defines an actual twelve-vertex, twenty-edge graph, records
ordered ports and ribbon orders, and retains both seam crossings. Its
frontiers are built from the same open wires used to construct the graph.
`WebMasks.stage_boundaries`, `stage_parabolics` and `stage_masks`
(`Guralnick/WebMasks.lean:49–73`) match the recorded stages to the actual
parabolic masks.

That is weaker than a theorem evaluating arbitrary ribbon graphs. In
particular, matching boundary data alone cannot rule out an extra internal
twist, different winding, or changed cyclic ordering. The algebraic proof
is still faithful to the manuscript's separately supplied integral-map
construction, but the project should continue to say that it has not
formalized the global annular presentation or the evaluation of its graph
as a morphism in that quotient category.

The new `FidelityWeb.lean` strengthens one concrete part of this bridge:
`family_frontiers` compares each recorded stage with edges selected directly
from the graph's source/target incidence across the corresponding vertex
cut. It checks source ports and thicknesses, not boundary ordering, accumulated
winding, an annular evaluation or an isotopy relation. `lake build
Guralnick.FidelityWeb` succeeds; `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Reproduction and trust

Run:

```sh
python3 scripts/audit_web_interfaces.py
lake build Guralnick.FidelityWeb
```

The Python report is `reports/fidelity-web-computations.json`. It is
explicitly **experimental**, uses no imported KL engine, and is not a proof
certificate accepted by Lean. Do not run Python with `-O`, which disables
assertions. The Lean graph-cut theorem uses kernel-checked proofs and no
additional mathematical hypotheses beyond `m>=2`.

These checks strengthen the semantic audit but do not prove existence of
the complete literature bundles. A successful conditional Lean theorem
still requires its external interfaces to be correct and jointly realizable.
