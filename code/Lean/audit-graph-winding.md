# Independent review of the graph, recuts and winding

30 October 2026. This records the independent critical review conducted
while the concrete graph-evaluation bridge was implemented. Its source
comparison concerns the unchanged `../main.tex`, especially the six-map
construction and the `StageBodyB` and `StageBodyC` TikZ macros. The bridge's
implementation report is separate: [audit-graph-evaluation.md](audit-graph-evaluation.md).

## Why the earlier check was insufficient

Equal boundary masks alone do not identify two web morphisms. Different
interior connections or windings can have the same masks. A faithful
bridge must consume actual ordered source ports, construct the actual
split and merge vertices, retain the seam crossings, and recover the
whole graph. The algebraic interpretation must then follow from the
general integral vertex maps, rather than being defined to be the desired
six-map answer.

This review specifically looked for a way in which an apparently harmless
change of cyclic boundary order might erase an annular turn.

## Comparison with the manuscript's actual pictures

The twelve trivalent vertices of `Web.family` resolve the six arrows in
`eq:integral-marked-web`. They agree with the pictured port order:

- In `StageBodyB`, the last m-edge crosses the chosen seam positively and
  enters the left-side merge before the original first m-edge. The middle
  unit strand bypasses the vertex. This is exactly the ordered merge
  `(right.wind 1, left)` in the existing graph.
- In `StageBodyC`, the first output m-edge of the cyclic split crosses the
  seam negatively and returns to the right. The other m-edge splits into
  `(1,m-1)` on the left; the returning edge splits into `(m-1,1)` on the
  right. This agrees with the graph's port order and identifies the two
  retained unit strands individually.
- The two inner merges and two inner splits leave those retained strands
  alone. The final merges attach each retained strand to its own neighbour.
  Their interchange, or an additional crossing between them, is not being
  hidden by an equality of packet sizes.

The graph's nonzero windings are therefore individually `+1` and `-1` on
the indicated m-edges. Zero total weighted winding does not mean that the
seam crossings were removed. The new ordered replay reproduces the
original entire graph, rather than replacing it with a graph chosen from
its boundary data.

The algebraic convention remains the manuscript's left-acting integral
composite, whose cleared expression is
`C_V C_K C_J C_W0 / (h_V h_L^2)`. The manuscript subsequently applies the
inverse-permutation anti-involution. That separate convention has not
been changed by the graph bridge.

## The full-turn objection and its resolution

An unrestricted rule that “cyclically rotate the wires, keep the same
parabolic, evaluate as identity” would be invalid. An entire annular turn
has nontrivial winding even though the parabolic mask returns to itself.
The manuscript explicitly retains coils and distinguishes winding from
the Hecke parameter. This was raised as a concrete design objection during
the implementation, not inferred away from a successful build.

The implemented replay grammar uses narrower operations:

- A right recut is available only at cut zero and only for a positive
  proper last packet.
- A left recut is available only at a positive cut when the first packet
  ends exactly at the zero cut.

These are chart changes for fixed global thin positions, with winding
retained on the moved edge. They are not arbitrary physical coils declared
to act trivially. The main trace uses cuts `0 -> m+1 -> 0`.

There are two independent formal checks of this interpretation.
`WebRecutPositions.occupied` records each actual live source port together
with every absolute thin residue occupied by its packet. The exact right
and left recut formulas prove that these named packets are cyclically
reordered without changing their occupied positions. Thus equal masks are
supported by stronger data identifying the individual wires.

Separately, `WebTraceWinding.charge` counts signed thickness-weighted
winding on both attached graph edges and still-live wires. The cut
potential is zero at cut zero and `N-cut` otherwise. Every successful
local operation preserves charge minus this potential. Finishing the
graph retains the live-wire winding. In particular, a successful trace
with zero exterior cuts cannot hide an entire annular turn.

This conservation statement does not assert that all degree-zero affine
morphisms are identities. The actual intermediate parabolics and their
split/merge maps remain in the composite, including the cyclic parabolic
containing `s_0`. Arbitrary winding operators are outside this restricted
recut grammar.

## Guards on the evaluated object

During review, two further safeguards were proposed and incorporated into
`PresentedGraph`: its actual input mass equals the Hecke rank, and its
actual graph is well formed. The structure also requires zero source and
target cuts. The concrete family satisfies these conditions by proved
lemmas; no condition about a desired canonical coefficient is introduced.

`WebPresentedWinding.seamDegree_zero` derives zero seam degree of the
actual graph from its successful replay and exterior cuts. The corollary
`not_presentable_of_nonzero_seam` rejects a graph of nonzero degree as an
admitted presentation. Thus an arbitrary winding loop cannot be passed
off as an identity-like recutting presentation.

Evaluation is attached to a **presented diagram**: the actual graph
with its checked ordered trace. This is precisely the extra structure
supplied by the manuscript's six-stage construction. It is not a claim
that every pair of arbitrary annular presentations has equal evaluation
whenever the drawings are isotopic.

## Proved supporting statements and reproduction

These are uniform Lean proofs, with no new literature assumptions:

| Module | Principal declarations |
|---|---|
| `WebTraceWinding.lean` | `step_mass`, `run_mass`, `step_charge`, `run_charge`, `finish_charge`, `run_zero_cut_seam`, `single_packet_turn_rejected`, `consecutive_right_rejected` |
| `WebRecutPositions.lean` | `right_recut`, `left_recut`, `step_right_positions`, `step_left_positions` |
| `WebPresentedWinding.lean` | `seamDegree_zero`, `not_presentable_of_nonzero_seam` |

```sh
lake build Guralnick.WebTraceWinding Guralnick.WebRecutPositions Guralnick.WebPresentedWinding
```

All three module builds passed during this review. Independent
`#print axioms` checks of the listed declarations reported only Lean's
standard `propext`, `Classical.choice` and `Quot.sound`, often a proper
subset. No family coefficient, canonical expansion, graph-evaluation
equality or cohomological identity is an assumption of these checks.

## Scope of the conclusion

This review found the restricted recuts consistent with the manuscript's
concrete cyclic split and merge: the actual named positions, vertex order
and winding are all retained. It does not construct the entire SSW
quotient category or prove all annular isotopy, braid and dot relations.
Those global claims are not needed for the specified integral six-map
construction.

The general finite-parabolic laws and the other entries of
`literature-inputs.md` remain explicit assumptions. Closing the concrete
graph-to-map connection does not turn the conditional counterexample into
an unconditional formal proof of all cited literature.
