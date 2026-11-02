import Guralnick.WebTraceBoundary
import Guralnick.WebTraceWinding
import Guralnick.WebExamples

/-! Regressions for the actual executable graph interpretation, including
rejection of invalid vertices, a full turn and erased seam data. -/
namespace Guralnick.WebTrace
open Web

theorem seed_replay : graph (familyInput 2) (familyTrace 2)=some seedGraph := by
  rw [family_graph 2 (by decide),seed_matches_builder]

theorem rank_three_replay : graph (familyInput 3) (familyTrace 3)=some (Web.family 3).graph :=
  family_graph 3 (by decide)

theorem rank_one_rejected : graph (familyInput 1) (familyTrace 1)=none := by decide

theorem wrong_split_rejected : step (.split 0 2 2) (initial (familyInput 2))=none := rfl

theorem missing_merge_wire_rejected : step (.merge 0) (initial (familyInput 2))=none := rfl

/-- An explicit change of the diagram: remove all its seam crossings. -/
def eraseWinding (g : Graph) : Graph :=
  {g with edges:=g.edges.map fun e => {e with winding:=0}}

theorem eraseWinding_crossings (g : Graph) :
    ((eraseWinding g).edges.map Edge.winding).filter (fun a => a != 0)=[] := by
  simp [eraseWinding,List.map_map,Function.comp_def]

/-- Equal total seam degree does not allow the two actual seam edges to be
removed. The entire graph comparison detects that change. -/
theorem family_ne_erased (m : Nat) :
    (Web.family m).graph≠eraseWinding (Web.family m).graph := by
  intro h
  have he:=congrArg (fun g : Graph =>
    (g.edges.map Edge.winding).filter (fun a => a != 0)) h
  dsimp only at he
  rw [Web.family_winding_list,eraseWinding_crossings] at he
  cases he

theorem erased_graph_rejected (m : Nat) (hm : 2≤m) :
    graph (familyInput m) (familyTrace m)≠some (eraseWinding (Web.family m).graph) := by
  rw [family_graph m hm]
  exact fun h => family_ne_erased m (Option.some.inj h)

end Guralnick.WebTrace
