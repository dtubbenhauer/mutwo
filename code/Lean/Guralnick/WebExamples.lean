import Guralnick.Web

/-!
# Kernel-checked concrete web data

The explicit m=2 edge list is separately written out and compared to the
six-stage builder. These checks concern the combinatorial graph and winding,
not canonical-basis coefficients or relations in a Schur algebra.
-/

namespace Guralnick.Web

/-- The twelve vertices of the displayed m=2 web, in construction order. -/
def seedGraph : Graph :=
  { input := ⟨0, [5]⟩
    output := ⟨0, [2, 1, 2]⟩
    vertices :=
      [⟨.split, 2, 3⟩, ⟨.split, 1, 2⟩, ⟨.merge, 2, 2⟩,
       ⟨.split, 2, 2⟩, ⟨.split, 1, 1⟩, ⟨.split, 1, 1⟩,
       ⟨.merge, 1, 1⟩, ⟨.merge, 2, 1⟩,
       ⟨.split, 1, 2⟩, ⟨.split, 1, 1⟩,
       ⟨.merge, 1, 1⟩, ⟨.merge, 1, 1⟩]
    edges :=
      [⟨.input 0, .vertex 0 0, 5, 0⟩,
       ⟨.vertex 0 1, .vertex 1 0, 3, 0⟩,
       ⟨.vertex 1 1, .vertex 2 0, 2, 1⟩,
       ⟨.vertex 0 0, .vertex 2 1, 2, 0⟩,
       ⟨.vertex 2 0, .vertex 3 0, 4, 0⟩,
       ⟨.vertex 3 1, .vertex 4 0, 2, 0⟩,
       ⟨.vertex 3 0, .vertex 5 0, 2, -1⟩,
       ⟨.vertex 4 1, .vertex 6 0, 1, 0⟩,
       ⟨.vertex 1 0, .vertex 6 1, 1, 0⟩,
       ⟨.vertex 6 0, .vertex 7 0, 2, 0⟩,
       ⟨.vertex 5 0, .vertex 7 1, 1, 0⟩,
       ⟨.vertex 7 0, .vertex 8 0, 3, 0⟩,
       ⟨.vertex 8 1, .vertex 9 0, 2, 0⟩,
       ⟨.vertex 4 0, .vertex 10 0, 1, 0⟩,
       ⟨.vertex 8 0, .vertex 10 1, 1, 0⟩,
       ⟨.vertex 9 1, .vertex 11 0, 1, 0⟩,
       ⟨.vertex 5 1, .vertex 11 1, 1, 0⟩,
       ⟨.vertex 10 0, .output 0, 2, 0⟩,
       ⟨.vertex 9 0, .output 1, 1, 0⟩,
       ⟨.vertex 11 0, .output 2, 2, 0⟩] }

theorem seed_matches_builder : (family 2).graph = seedGraph := by rfl

theorem seed_wellFormed : seedGraph.WellFormed := by decide

theorem seed_conservation :
    (List.range 12).all (fun i =>
      decide (seedGraph.incomingMass i = seedGraph.outgoingMass i)) = true := by
  decide

theorem seed_boundaries :
    (family 2).boundaries =
      [⟨0, [5]⟩, ⟨0, [2, 1, 2]⟩, ⟨3, [4, 1]⟩,
       ⟨0, [1, 1, 1, 1, 1]⟩, ⟨0, [1, 3, 1]⟩,
       ⟨0, [1, 1, 1, 1, 1]⟩, ⟨0, [2, 1, 2]⟩] := by rfl

theorem rank_three_boundaries :
    (family 3).boundaries =
      [⟨0, [7]⟩, ⟨0, [3, 1, 3]⟩, ⟨4, [6, 1]⟩,
       ⟨0, [1, 2, 1, 2, 1]⟩, ⟨0, [1, 5, 1]⟩,
       ⟨0, [1, 2, 1, 2, 1]⟩, ⟨0, [3, 1, 3]⟩] := by rfl

theorem seed_cyclic_positions : cyclicPositions 5 3 4 = [4, 5, 1, 2] := by decide

theorem rank_three_cyclic_positions :
    cyclicPositions 7 4 6 = [5, 6, 7, 1, 2, 3] := by decide

theorem rank_three_wellFormed : (family 3).graph.WellFormed :=
  family_wellFormed 3 (by decide)

theorem rank_five_wellFormed : (family 5).graph.WellFormed :=
  family_wellFormed 5 (by decide)

/-- The thin retained strands connect stage (c) directly to stage (f),
bypassing both internal middle operations. -/
theorem seed_retained_strands :
    ⟨.vertex 4 0, .vertex 10 0, 1, 0⟩ ∈ seedGraph.edges ∧
    ⟨.vertex 5 1, .vertex 11 1, 1, 0⟩ ∈ seedGraph.edges := by decide

theorem seed_winding_edges :
    seedGraph.edges.filter (fun e => e.winding != 0) =
      [⟨.vertex 1 1, .vertex 2 0, 2, 1⟩,
       ⟨.vertex 3 0, .vertex 5 0, 2, -1⟩] := by decide

/-- A nonzero winding remains even though its signed weighted sum is zero. -/
theorem seed_winding_is_not_erased :
    seedGraph.seamDegree = 0 ∧
    seedGraph.edges.any (fun e => e.winding != 0) = true := by decide

/-- The positive-label hypothesis is substantive: the literal construction
at m=1 contains zero-thickness edges and fails this graph's well-formedness
test. A web category may separately erase zero labels; we do not do so here. -/
theorem rank_one_needs_zero_edge_contraction : ¬ (family 1).graph.WellFormed := by
  intro h
  have hv := h.2.2.1
  have bad : (family 1).graph.vertices.all
      (fun v => decide (0 < v.a ∧ 0 < v.b)) = false := by rfl
  rw [bad] at hv
  cases hv

end Guralnick.Web
