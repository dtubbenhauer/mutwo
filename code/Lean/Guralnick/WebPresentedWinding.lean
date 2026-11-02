import Guralnick.WebTraceEvaluation
import Guralnick.WebTraceWinding

/-!
# Degree zero of the evaluated cut-open graph presentation

The graph is recovered from its actual checked trace, with zero source and
target cuts. Winding conservation therefore proves degree zero of the graph
itself. The algebraic evaluator does not silently identify an arbitrary
positive full turn with identity.
-/
namespace Guralnick.WebPresentedWinding
open Web WebTrace WebTraceEvaluation WebTraceWinding

/-- Every admitted ordinary-boundary presentation has zero actual signed
thickness-weighted seam degree, as a consequence of replay. -/
theorem seamDegree_zero {n : Nat} {hn : 0<n} {g : Graph}
    (P : PresentedGraph hn g) : g.seamDegree=0 := by
  have ht : P.target.cut=0 := by
    calc
      P.target.cut=(P.target.finish g.input).output.cut := rfl
      _=g.output.cut := congrArg (fun z : Graph => z.output.cut) P.realizes
      _=0 := P.targetCut
  have h:=run_zero_cut_seam P.sourceCut ht (Program.replay hn P.program)
  rw [P.realizes] at h
  exact h

/-- A diagram with nonzero winding degree cannot acquire an identity-like
interpretation by being passed off as one of these zero-cut presentations. -/
theorem not_presentable_of_nonzero_seam {n : Nat} {hn : 0<n} {g : Graph}
    (h : g.seamDegree≠0) : ¬Nonempty (PresentedGraph hn g) := by
  rintro ⟨P⟩
  exact h (seamDegree_zero P)

end Guralnick.WebPresentedWinding
