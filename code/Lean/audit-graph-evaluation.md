# Closing the concrete graph-evaluation gap

30 October 2026. This note concerns the precise gap recorded in the
previous fidelity audit: the graph and the six-map integral element were
separately defined, with no theorem connecting them. The new bridge checks
the paper's fixed cut-open presentation, including its two seam crossings.
The manuscript has not been edited.

## What is now proved

`WebTraceEvaluation.family_graph_evaluation_eq_raw` proves, uniformly for
`m>=2`, that evaluation of `familyPresentedGraph hm` equals
`ParabolicWeb.Family.raw`. Evaluation is not defined to be that raw element.
It recursively interprets the actual local graph events, and the equality
follows from the independently proved composition laws for integral maps.

The construction has three independently checked parts:

1. `WebTrace.family_step` executes all fourteen operations on the actual
   ordered live graph ports: twelve trivalent vertices and two canonical
   recuts. `familyState_graph` identifies the entire resulting graph with
   `Web.family`, including every edge, vertex port, thickness, winding and
   ordered boundary. `familyState_frontier` and `familyState_boundary`
   identify the displayed stages and all intermediate local boundaries.
2. `WebBoundary.index` computes each finite parabolic from the cut and
   ordered partial sums of the actual packet sizes. Every local refinement
   direction is proved. These computations include the affine generator
   `s_0` in the cyclic parabolic; the cyclic step is not replaced by an
   ordinary finite merge at the zero cut.
3. `WebTraceEvaluation.Event` requires both a successful actual graph
   operation and its corresponding direction on those computed parabolics.
   Its map is the integral inclusion for a split, the integral merge for a
   merge, and the identification of the same absolute-position module for
   a checked recut. A `Program` composes these maps and proves that its
   operations replay to its actual final graph state.

`PresentedGraph` additionally requires the graph to be well formed, its
input mass to equal the Hecke rank, and both exterior cuts to be zero.
All these requirements are proved for the concrete family; none becomes
an extra hypothesis about its coefficients or a new literature assumption.

## Why binary resolution and choice of merge do not matter

`WebEvaluation.merge_linear_unique` proves that the action
`C_I*h -> C_J*h` on every generator determines an integral merge uniquely.
`merge_comp_unique` proves that two consecutive merges give the direct
merge. Composition of two splits is composition of actual inclusions.

`WebEvaluationCompression.Resolution.fine_linear_eq_coarse` applies these
laws to the twelve binary vertices and produces the six multi-splits and
merges. The concrete `familyResolution` takes its intermediate indices
from the literal local boundaries. The final comparison uses
`merge_value_congr`: proved identification of source and target parabolics,
and equality of ambient inputs, imply equality of merge outputs. This
makes the equality transports at the recuts explicit.

Thus the equality is derived from local maps and actual graph data. No
canonical coefficient, row sum, or desired final answer occurs in the
trace evaluator's definition.

## Winding is checked, not discarded

A recut is restricted to a canonical change between the zero cut and one
packet boundary. An arbitrary rotation or full annular turn is not an
operation interpreted as identity. The ordered replay attaches `+1` and
`-1` to the individual moved edges, and reproduces the graph's two actual
nonzero edge windings.

`WebRecutPositions` proves that a successful recut preserves each named
live wire's absolute thin-position packet. `WebTraceWinding` proves
conservation of the actual winding charge along replay. The identities of
parabolic modules therefore express a change of chart in absolute
positions; they do not identify an arbitrary winding morphism with an
identity map. The separate winding audit records the resulting protection
against a silently erased full turn.

## Assumptions and exact scope

The graph-evaluation theorem has only `m>=2`, the existing actual
`Hecke.KLRealization`, the existing general finite-parabolic longest data,
and `ParabolicWeb.Laws` as parameters. These are the same general algebraic
framework inputs already listed in `literature-inputs.md`. No new external
mathematical input was introduced to close the bridge.

This evaluates the paper's **specified cut-open presentation** of the
concrete graph. It is not a construction of the entire SSW quotient
category, nor a proof that every pair of arbitrary annular presentations
has the same evaluation whenever they are isotopic. Those global claims
are not used by this fixed six-map proof. The representation-theoretic
literature inputs remain unformalized as before; this addition does not
turn the final conditional counterexample into an unconditional Lean
proof of the entire literature.

## Reproduction

```sh
lake build Guralnick.WebFamilyEvaluation
```

The central declarations are:

- `WebEvaluation.merge_linear_unique`, `merge_comp_unique`;
- `WebTraceEvaluation.Program.replay`, `PresentedGraph.replay`;
- `WebTraceEvaluation.familyProgram_operations`;
- `WebTraceEvaluation.familyPresentedGraph_replay`;
- `WebTraceEvaluation.familyProgram_raw_eq_fine`;
- `WebTraceEvaluation.family_graph_evaluation_eq_raw`.

The full project verification and principal axiom audit are recorded in
`status.md` and `reports/verification.json`. The standalone module build
passed during implementation. A separate `#print axioms` check of all eight
listed declarations reports only `propext`, `Classical.choice` and
`Quot.sound`; its output is `reports/graph-evaluation-axioms.txt`. No new
mathematical axiom or proof escape was used.
