import Guralnick.Web
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.FinCases

/-!
# Independent check of the recorded frontiers against actual graph cuts

The open edges are selected directly from the graph's source/target ports
and the cut between trivalent vertices. This definition does not inspect
the stored frontiers. The theorem verifies each stored stage's incidence
and thickness data against that independent cut. It is not an evaluation
in a web category, nor a theorem of annular embeddability or isotopy.

An edge's total winding can occur after a selected cut; the theorem does
not equate that total with the winding accumulated by an open wire so far.
-/
namespace Guralnick.FidelityWeb
open Web

/-- A directed edge is open after exactly `cut` trivalent vertices. -/
def crosses (cut : Nat) (e : Edge) : Bool :=
  (match e.source with
   | .input _ => true
   | .vertex i _ => decide (i<cut)
   | .output _ => false) &&
  (match e.target with
   | .output _ => true
   | .vertex i _ => decide (cut≤i)
   | .input _ => false)

/-- Actual open source ports and thicknesses at a graph cut. -/
def actualFrontier (g : Graph) (cut : Nat) : List (End × Nat) :=
  ((g.edges.filter (crosses cut)).map fun e => (e.source,e.thickness))

/-- Seven cuts, including the input cut, at the manuscript's six stages. -/
def stageCut (stage : Fin 7) : Nat := [0,2,3,6,8,10,12].getD stage.val 0

/-- The stored wire list is only used on the right side of the comparison. -/
def recordedFrontier (f : Web.Family) (stage : Fin 7) : List (End × Nat) :=
  ((f.frontiers.getD stage.val (0,[])).2).map fun w => (w.source,w.thickness)

/-- Every recorded stage consists exactly of the graph edges crossing the
corresponding cut, with the correct thickness on each source port. -/
theorem family_frontiers (m : Nat) (hm : 2≤m) (stage : Fin 7) :
    (actualFrontier (family m).graph (stageCut stage)).Perm
      (recordedFrontier (family m) stage) := by
  have h₁ : 1+(m-1)=m := by omega
  have h₂ : (m-1)+1=m := by omega
  have h₃ : m+(m-1)=2*m-1 := by omega
  fin_cases stage <;>
    simp only [actualFrontier,recordedFrontier,stageCut,family,Builder.split,
      Builder.merge,Builder.finish,Wire.wind,List.length_cons,List.length_nil,
      List.cons_append,List.nil_append,List.zipIdx_cons,
      List.zipIdx_nil,List.map_cons,List.map_nil,List.getD_cons_zero,
      List.getD_cons_succ]
  all_goals
    simp [crosses,List.perm_iff_count,List.count_cons,h₁,h₂,h₃,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

#print axioms family_frontiers
end Guralnick.FidelityWeb
