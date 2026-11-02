import Guralnick.WebTraceCore
import Guralnick.WebBoundary

/-!
# A thin seam regression

In three thin positions the ordinary first merge has parabolic index
{s_1}, whereas the actual merge of the last and first wires across the
cut has index {s_0}. Thus interpreting a canonical recut as a chart change
does not replace the affine generator by an ordinary finite generator.
The closing split returns to cut zero and retains both individual seam
crossings in the resulting graph.
-/
namespace Guralnick.WebTraceSeamExample
open Web WebTrace

def thinInput : Boundary := ⟨0,[1,1,1]⟩
def start : State := initial thinInput

def ordinaryMerge : Option State := run [.merge 0] start
def seamMerge : Option State := run [.rotateRight,.merge 0] start

def ordinaryIndex : ParabolicWeb.Index 3 := ⟨{(1 : Fin 3)},by decide⟩
def seamIndex : ParabolicWeb.Index 3 := ⟨{(0 : Fin 3)},by decide⟩

def actualIndex (s : State) : ParabolicWeb.Index 3 :=
  WebBoundary.index (by decide : 0<3) s.boundary

/-- This checks the actual local replay, not an independently prescribed mask. -/
theorem ordinary_merge_index : ordinaryMerge.map actualIndex=some ordinaryIndex := by
  apply congrArg some
  apply Subtype.ext
  decide

theorem seam_merge_index : seamMerge.map actualIndex=some seamIndex := by
  apply congrArg some
  apply Subtype.ext
  decide

theorem ordinary_merge_boundary :
    ordinaryMerge.map State.boundary=some ⟨0,[2,1]⟩ := by decide

theorem seam_merge_boundary :
    seamMerge.map State.boundary=some ⟨2,[2,1]⟩ := by decide

theorem seam_is_affine :
    (0 : Fin 3)∈seamIndex.val ∧ (0 : Fin 3)∉ordinaryIndex.val ∧
      ordinaryIndex≠seamIndex := by
  refine ⟨by decide,by decide,?_⟩
  intro h
  have hzero : (0 : Fin 3)∈ordinaryIndex.val := by rw [h]; decide
  exact (by decide : (0 : Fin 3)∉ordinaryIndex.val) hzero

/-- Actual cyclic merge--split, with the two canonical chart changes. -/
def seamChannel : List Op := [.rotateRight,.merge 0,.split 0 1 1,.rotateLeft]

def seamChannelGraph : Graph :=
  { input:=thinInput
    output:=thinInput
    vertices:=[⟨.merge,1,1⟩,⟨.split,1,1⟩]
    edges:=[⟨.input 2,.vertex 0 0,1,1⟩,
      ⟨.input 0,.vertex 0 1,1,0⟩,
      ⟨.vertex 0 0,.vertex 1 0,2,0⟩,
      ⟨.vertex 1 1,.output 0,1,0⟩,
      ⟨.input 1,.output 1,1,0⟩,
      ⟨.vertex 1 0,.output 2,1,-1⟩] }

theorem seam_channel_replay : graph thinInput seamChannel=some seamChannelGraph := by decide

theorem seam_channel_wellFormed : seamChannelGraph.WellFormed := by decide

/-- Zero total winding does not discard the two nonzero winding edges. -/
theorem seam_channel_winding :
    seamChannelGraph.seamDegree=0 ∧
      (seamChannelGraph.edges.map Edge.winding).filter (fun k => k != 0)=[1,-1] := by decide

end Guralnick.WebTraceSeamExample
