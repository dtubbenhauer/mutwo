# From the actual web graph to the six integral maps

The earlier fidelity audit identified a precise missing theorem: the
separately defined graph had no proved evaluation equal to the element
used in the algebraic calculation. The new construction supplies that
bridge for the manuscript's concrete, cut-open presentation. It adds no
literature hypothesis and changes no manuscript statement.

## What is evaluated

`Web.family m` remains the original twelve-vertex, twenty-edge graph.
It contains ordered local ports, explicit incidences, edge thicknesses,
ordered boundaries and signed edge windings. It has not been replaced
by a list of the desired six parabolic maps.

`WebTraceCore` defines an independent executable interpreter. Its state
contains the graph built so far, the ordered live wires and the current
cut. A split consumes one actual live port; a merge consumes two adjacent
live ports. The interpreter checks positivity and the sum of thicknesses,
creates the trivalent vertex, and attaches the consumed graph edges with
their actual windings. Invalid operations return `none`.

The family trace has fourteen operations: twelve binary vertices and two
changes of cut. `WebTrace.family_step` checks every operation uniformly
for `m>=2`. `WebTrace.family_graph` proves that the resulting entire graph
is exactly the existing `Web.family m`, including its individual edge
windings. `family_frontier` proves equality of the ordered live wires,
with their accumulated windings, at all seven manuscript stages.

## Why a seam move is not discarded

Arbitrary rotations cannot be interpreted as identity: a full annular
turn carries genuine winding. The interpreter therefore admits only the
two canonical recuts used here. A right recut starts at cut zero and moves
a positive proper last packet to the front. The inverse recut is allowed
only when the first packet ends exactly at the zero cut. The family follows
`0 -> m+1 -> 0`.

Two independent checks make the meaning precise:

- `WebRecutPositions.step_right_positions` and `step_left_positions`
  preserve the actual absolute thin residues of every named live port.
  The exact cyclic-list identities are `right_recut` and `left_recut`.
- `WebTraceWinding.step_charge` and `run_charge` track the weighted winding
  on both completed edges and live wires. They preserve winding minus the
  cut potential. A sole-packet full turn and consecutive right recuts are
  rejected. Ordinary input and output cuts force zero total seam degree,
  while the separate `+1` and `-1` edges remain in the graph.

The module at a boundary is determined by its absolute-position cuts.
Thus the cyclic merge uses the affine parabolic containing `s_0`.
Interpreting a canonical recut as a chart identification does not turn
that parabolic into an ordinary one or erase its subsequent map.
The `WebTraceSeamExample` regression checks the distinction explicitly in
three thin positions: the ordinary adjacent merge gives `{s_1}`, while
the seam merge gives `{s_0}`.

## How the algebraic map is obtained

`WebBoundary.index` calculates the omitted affine generators from the
actual ordered packet sizes and cut. All fifteen local boundaries are
checked independently against the replay states. `local_relations`
proves the direction of every inclusion and the two chart equalities.

An `Event` in `WebTraceEvaluation` includes an actual successful replay
step. Its vertex type determines its algebraic interpretation:

- split: the actual inclusion of spherical right ideals;
- merge: the integral map `C_I*h -> C_J*h` supplied by the existing general
  finite-parabolic interface;
- canonical recut: transport between the two descriptions of the same
  absolute-position boundary.

A `Program` composes those events. A `PresentedGraph` requires the correct
mass, ordinary endpoint cuts, graph well-formedness and equality of its
*entire* graph with the replay output. The evaluation is computed from
its events. Neither the six-map raw element nor any coefficient is a field
of this structure.

`WebEvaluation.merge_linear_unique` proves uniqueness from the action on
all cyclic generators. Together with composition of actual inclusions,
this gives the split/merge composition laws. The twelve local vertices
therefore compress to the six maps by
`WebEvaluationCompression.Resolution.fine_linear_eq_coarse`.

The central theorem is
`WebTraceEvaluation.family_graph_evaluation_eq_raw` in
[Guralnick/WebFamilyEvaluation.lean](Guralnick/WebFamilyEvaluation.lean):

```
(familyPresentedGraph hm).evaluate hn K D L
  = ParabolicWeb.Family.raw K D L
```

Here `K`, `D` and `L` are the same general KL, longest-parabolic and
integral-map inputs already used in the original algebraic proof. The
identity is proved from replay, boundary calculations and map composition;
it is not the definition of `evaluate`.

`WebRightLinearity` additionally proves that every interpreted event and
program commutes with actual right Hecke multiplication. Its value on the
spherical generator determines the entire right-module morphism. Thus
using the evaluated raw element in the canonical-basis calculation is
not a substitute for defining a web morphism. The stronger theorem
`WebProof.graph_morphism_eq_sixMaps` proves equality of the entire interpreted
morphism with the paper's six-map morphism. `WebGraphProof.lean` then
transfers every standard and canonical coordinate and proves the corrected
graph's critical value. `WebProof.graph_critical_eq_row_sum` identifies that
readout with the ordinary fixed-source KL row.

## Exact scope and verification

The result evaluates the paper's **specified graph presentation**. It does
not assert that every presentation of an arbitrary annular ribbon graph
has the same evaluation, construct the whole SSW quotient category, or
prove every braid, dot and isotopy relation. A general physical coil is
not a constructor of this restricted trace language. Those broader
presentation questions must not be confused with the specific bridge
proved here.

The graph-bridge implementation did not change the general literature
assumptions listed in [literature-inputs.md](literature-inputs.md). A source-hash comparison against the preserved pre-bridge
report confirms that the general interface files were not changed; see
`reports/graph-assumptions-unchanged.json` and
`reports/pre-graph-verification.json`. Those reports describe that earlier
step. The subsequent [assumption reduction](audit-assumption-reduction.md)
removes three input fields by proving them; its separate comparison is
`reports/literature-assumption-reduction.json`. The counterexample remains
conditional on the remaining inputs; neither step formalizes all cited papers.

Run from this directory:

```sh
lake build
lake env lean Guralnick/AxiomAudit.lean
python3 scripts/verify.py
```

`WebTraceExamples` contains kernel-checked seed and rank-three replays,
rejection at rank one, invalid split/merge rejection, and a proof that the
same replay cannot produce the graph with its winding erased. The current
combined build and axiom results are in [status.md](status.md).
The implementation review is
[audit-graph-evaluation.md](audit-graph-evaluation.md). The independent
picture, winding and chart-semantics review is
[audit-graph-winding.md](audit-graph-winding.md).


A further [lattice verification](audit-lattice-completion.md) now constructs
the general lattice-theory bundle and removes that premise from the external
input. The graph and six-map definitions are unchanged. The source comparison
for this subsequent step is `reports/lattice-assumption-reduction.json`.
