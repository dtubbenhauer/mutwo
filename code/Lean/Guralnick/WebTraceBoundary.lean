import Guralnick.WebTrace
import Guralnick.WebBoundary

/-! The checked local graph replay has exactly the absolute-position
boundaries used for the integral parabolic interpretation. -/
namespace Guralnick.WebTrace
open Web

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem familyState_boundary (m : Nat) (hm : 2≤m) (stage : Fin 15) :
    (familyState m stage).boundary=WebBoundary.Family.boundary m stage := by
  have h₁ : 1+(m-1)=m := by omega
  have h₂ : (m-1)+1=m := by omega
  have h₃ : m+(m-1)=2*m-1 := by omega
  fin_cases stage <;>
    simp [familyState,familyStates,State.boundary,WebBoundary.Family.boundary,
      Builder.split,Builder.merge,Wire.wind,h₁,h₂,h₃,Nat.two_mul]

theorem run_append (as bs : List Op) (s : State) :
    run (as++bs) s=(run as s).bind (run bs) := by
  induction as generalizing s with
  | nil => simp [run]
  | cons op ops ih => simp [run,ih,Option.bind_assoc]

theorem run_take_succ (ops : List Op) (s : State) (i : Nat) (hi : i<ops.length) :
    run (ops.take (i+1)) s = (run (ops.take i) s).bind (step (ops.get ⟨i,hi⟩)) := by
  rw [List.take_succ_eq_append_getElem hi,run_append]
  simp [run]

/-- The raw executable replay succeeds at every prefix and yields exactly
the independently constructed live-port state. -/
theorem runPrefix_state (m : Nat) (hm : 2≤m) (stage : Fin 15) :
    runPrefix m stage.val=some (familyState m stage) := by
  suffices ∀ k (hk : k<15), runPrefix m k=some (familyState m ⟨k,hk⟩) by
    exact this stage.val stage.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    rfl
  | succ k ih =>
    intro hk
    have hk₁ : k<14 := by omega
    have hk₂ : k<(familyTrace m).length := by simpa only [familyTrace,List.length_cons,List.length_nil] using hk₁
    rw [runPrefix,run_take_succ _ _ _ hk₂]
    change (runPrefix m k).bind _=some _
    rw [ih (by omega),Option.bind_some]
    exact family_step m hm ⟨k,hk₁⟩

/-- The literal graph replay, including winding and local port order,
produces the graph already used to record the manuscript diagram. -/
theorem family_graph (m : Nat) (hm : 2≤m) :
    graph (familyInput m) (familyTrace m)=some (Web.family m).graph := by
  have h:=runPrefix_state m hm (14 : Fin 15)
  have ht : (familyTrace m).take 14=familyTrace m := by rfl
  change run ((familyTrace m).take 14) (initial (familyInput m))=some (familyState m 14) at h
  rw [ht] at h
  rw [graph,h,Option.map_some,familyState_graph]

/-- Exact frontier equality along execution, not only equality of abstract
boundary masks or unordered thicknesses. -/
theorem family_frontier (m : Nat) (hm : 2≤m) (stage : Fin 7) :
    (runPrefix m (checkpoint stage)).map State.frontier =
      some ((Web.family m).frontiers.getD stage.val (0,[])) := by
  rw [runPrefix_state m hm ⟨checkpoint stage,by fin_cases stage <;> decide⟩,
    Option.map_some,familyState_frontier]

end Guralnick.WebTrace
