import Guralnick.WebTraceCore

namespace Guralnick.WebTrace
open Web

/-- Independently constructed live-port states for the manuscript's graph.
These use the graph builder, not `step` or the execution of `familyTrace`.
The local replay theorem below checks that every listed state follows by
one genuine checked operation. -/
def familyStates (m : Nat) : List State :=
  let input : Wire := ⟨.input 0,2*m+1,0⟩
  let (left,rest,s₀) := Builder.split {} input m (m+1)
  let (centre,right,s₁) := s₀.split rest 1 m
  let (cyclic,s₂) := s₁.merge (right.wind 1) left
  let (right₀,left₀,s₃) := s₂.split cyclic m m
  let (keepL,innerL,s₄) := s₃.split left₀ 1 (m-1)
  let (innerR,keepR,s₅) := s₄.split (right₀.wind (-1)) (m-1) 1
  let (middle₀,s₆) := s₅.merge innerL centre
  let (middle,s₇) := s₆.merge middle₀ innerR
  let (innerL',rest',s₈) := s₇.split middle (m-1) m
  let (centre',innerR',s₉) := s₈.split rest' 1 (m-1)
  let (left',s₁₀) := s₉.merge keepL innerL'
  let (right',s₁₁) := s₁₀.merge innerR' keepR
  [⟨{},[input],0⟩,
   ⟨s₀,[left,rest],0⟩,
   ⟨s₁,[left,centre,right],0⟩,
   ⟨s₁,[right.wind 1,left,centre],m+1⟩,
   ⟨s₂,[cyclic,centre],m+1⟩,
   ⟨s₃,[right₀,left₀,centre],m+1⟩,
   ⟨s₄,[right₀,keepL,innerL,centre],m+1⟩,
   ⟨s₄,[keepL,innerL,centre,right₀.wind (-1)],0⟩,
   ⟨s₅,[keepL,innerL,centre,innerR,keepR],0⟩,
   ⟨s₆,[keepL,middle₀,innerR,keepR],0⟩,
   ⟨s₇,[keepL,middle,keepR],0⟩,
   ⟨s₈,[keepL,innerL',rest',keepR],0⟩,
   ⟨s₉,[keepL,innerL',centre',innerR',keepR],0⟩,
   ⟨s₁₀,[left',centre',innerR',keepR],0⟩,
   ⟨s₁₁,[left',centre',right'],0⟩]

def familyState (m : Nat) (stage : Fin 15) : State := (familyStates m).get stage

theorem familyState_zero (m : Nat) : familyState m 0=initial (familyInput m) := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Every actual event is a valid local operation on the ordered live graph
ports. No adjacency, split label or seam winding is inferred from a mask. -/
theorem family_step (m : Nat) (hm : 2≤m) (stage : Fin 14) :
    step ((familyTrace m).get stage) (familyState m stage.castSucc)=
      some (familyState m stage.succ) := by
  have h₁ : 0<m := by omega
  have h₂ : 0<m-1 := by omega
  have h₃ : 2*m+1=m+(m+1) := by omega
  have h₄ : m+1=1+m := by omega
  have h₅ : 1+(m-1)=m := by omega
  have h₆ : (m-1)+1=m := by omega
  fin_cases stage <;>
    simp (disch := omega) [familyTrace,familyState,familyStates,step,
      State.mass,State.boundary,Boundary.mass,Builder.split,Builder.merge,
      Wire.wind,h₁,h₂,h₃,h₄,h₅,h₆] <;> omega

theorem familyState_graph (m : Nat) :
    (familyState m 14).finish (familyInput m)=(Web.family m).graph := rfl

/-- Exact ordered live wires, with their accumulated winding, at all seven
manuscript checkpoints. -/
theorem familyState_frontier (m : Nat) (stage : Fin 7) :
    (familyState m ⟨checkpoint stage,by fin_cases stage <;> decide⟩).frontier =
      (Web.family m).frontiers.getD stage.val (0,[]) := by
  fin_cases stage <;> rfl

end Guralnick.WebTrace
