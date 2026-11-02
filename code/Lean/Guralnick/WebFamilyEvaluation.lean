import Guralnick.WebTraceEvaluation
import Guralnick.WebTraceBoundary
import Guralnick.WebEvaluationCompression

/-!
# The checked concrete graph as an integral parabolic morphism

Each of the fourteen events below is the actual ordered local operation
used to construct the graph. Its boundary index is calculated from the
literal live wires and cut, and the direction of its integral map is
checked against that calculation.
-/
noncomputable section
set_option maxRecDepth 5000
set_option maxHeartbeats 1500000
namespace Guralnick.WebTraceEvaluation
open Hecke ParabolicWeb WebTrace WebEvaluation

/-- Integral merge evaluation is invariant under proved identification of
its actual source/target parabolics and equality of its ambient input.
This avoids hiding equality transports in the graph calculation. -/
theorem merge_value_congr {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
    (D : ∀ I : Index n, LongestData c I) (L : Laws K D)
    {I J I' J' : Index n} {h : I.val⊆J.val} {h' : I'.val⊆J'.val}
    {x : ModuleAt K D I} {x' : ModuleAt K D I'}
    (hI : I=I') (hJ : J=J') (hx : x.val=x'.val) :
    (WebEvaluation.merge K D L h x).val=(WebEvaluation.merge K D L h' x').val := by
  subst I'
  subst J'
  have he : x=x' := Subtype.ext hx
  subst x'
  rfl

variable {m : ℕ} (hm : 2≤m)

theorem stateIndex_family (stage : Fin 15) :
    stateIndex (show 0<2*m+1 by omega) (familyState m stage)=WebBoundary.Family.idx hm stage := by
  unfold stateIndex WebBoundary.Family.idx
  rw [familyState_boundary m hm stage]

def familyEvent (stage : Fin 14) : Event (show 0<2*m+1 by omega)
    (familyState m stage.castSucc) (familyState m stage.succ) where
  op := (familyTrace m).get stage
  replay := family_step m hm stage
  compatible := by
    rw [stateIndex_family hm,stateIndex_family hm]
    rcases WebBoundary.Family.local_relations hm with
      ⟨h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃⟩
    fin_cases stage
    · exact h₀
    · exact h₁
    · exact h₂.symm
    · exact h₃
    · exact h₄
    · exact h₅
    · exact h₆.symm
    · exact h₇
    · exact h₈
    · exact h₉
    · exact h₁₀
    · exact h₁₁
    · exact h₁₂
    · exact h₁₃

def familyProgram : Program (show 0<2*m+1 by omega) (familyState m 0) (familyState m 14) :=
  ((((((((((((((Program.nil (familyState m 0)).snoc (familyEvent hm 0)).snoc
    (familyEvent hm 1)).snoc (familyEvent hm 2)).snoc (familyEvent hm 3)).snoc
    (familyEvent hm 4)).snoc (familyEvent hm 5)).snoc (familyEvent hm 6)).snoc
    (familyEvent hm 7)).snoc (familyEvent hm 8)).snoc (familyEvent hm 9)).snoc
    (familyEvent hm 10)).snoc (familyEvent hm 11)).snoc (familyEvent hm 12)).snoc
    (familyEvent hm 13)

/-- The evaluator consumes exactly the operation list that generated the
entire graph, with both signed recuts retained. -/
theorem familyProgram_operations : (familyProgram hm).operations=familyTrace m := by
  simp [familyProgram,Program.operations,familyEvent,familyTrace]

/-- A presentation of the actual graph, with full edge/port/winding equality. -/
def familyPresentedGraph : PresentedGraph (show 0<2*m+1 by omega) (Web.family m).graph where
  inputMass := by rfl
  sourceCut := by rfl
  targetCut := by rfl
  wellFormed := Web.family_wellFormed m hm
  target := familyState m 14
  program := familyProgram hm
  realizes := familyState_graph m

theorem familyPresentedGraph_replay :
    WebTrace.graph (Web.family m).graph.input (familyProgram hm).operations=
      some (Web.family m).graph :=
  (familyPresentedGraph hm).replay _

/-- Binary cut data are extracted from the actual fifteen graph states. -/
def familyResolution : WebEvaluationCompression.Resolution
    (ParabolicWeb.Family.source m) (ParabolicWeb.Family.output m)
    (ParabolicWeb.Family.cyclic m) (ParabolicWeb.Family.common m)
    (ParabolicWeb.Family.middle m) where
  A := WebBoundary.Family.idx hm 1
  B := WebBoundary.Family.idx hm 5
  C := WebBoundary.Family.idx hm 6
  D := WebBoundary.Family.idx hm 9
  E := WebBoundary.Family.idx hm 11
  F := WebBoundary.Family.idx hm 13
  h₀A := by
    simpa only [WebBoundary.Family.idx_source] using (WebBoundary.Family.local_relations hm).1
  hAV := by
    simpa only [WebBoundary.Family.idx_output] using (WebBoundary.Family.local_relations hm).2.1
  hVJ := by
    have h₂ := (WebBoundary.Family.local_relations hm).2.2.1
    simpa only [h₂,WebBoundary.Family.idx_output,WebBoundary.Family.idx_cyclic] using (WebBoundary.Family.local_relations hm).2.2.2.1
  hJB := by
    simpa only [WebBoundary.Family.idx_cyclic] using (WebBoundary.Family.local_relations hm).2.2.2.2.1
  hBC := by
    exact (WebBoundary.Family.local_relations hm).2.2.2.2.2.1
  hCL := by
    have h₆ := (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.1
    simpa only [h₆,WebBoundary.Family.idx_common] using (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.2.1
  hLD := by
    simpa only [WebBoundary.Family.idx_common] using (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.2.2.1
  hDK := by
    simpa only [WebBoundary.Family.idx_middle] using (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.2.2.2.1
  hKE := by
    simpa only [WebBoundary.Family.idx_middle] using (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.2.2.2.2.1
  hEL := by
    simpa only [WebBoundary.Family.idx_common_again] using (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.2.2.2.2.2.1
  hLF := by
    simpa only [WebBoundary.Family.idx_common_again] using (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.2.2.2.2.2.2.1
  hFV := by
    simpa only [WebBoundary.Family.idx_output_again] using (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.2.2.2.2.2.2.2

theorem familyResolution_coarse :
    (familyResolution hm).coarsePath=WebEvaluation.Family.path m := by rfl

variable {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
variable (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)

/-- Replaying local graph events and interpreting their literal cuts gives
exactly the binary integral refinement path. Neither side is defined by
its desired canonical coefficients. -/
theorem familyProgram_raw_eq_fine :
    (familyProgram hm).raw (show 0<2*m+1 by omega) K D L=
      Path.raw K D L (familyResolution hm).finePath := by
  have hs0 : Fin.succ (0 : Fin 14)=(1 : Fin 15) := rfl
  have hs1 : Fin.succ (1 : Fin 14)=(2 : Fin 15) := rfl
  have hs2 : Fin.succ (2 : Fin 14)=(3 : Fin 15) := rfl
  have hs3 : Fin.succ (3 : Fin 14)=(4 : Fin 15) := rfl
  have hs4 : Fin.succ (4 : Fin 14)=(5 : Fin 15) := rfl
  have hs5 : Fin.succ (5 : Fin 14)=(6 : Fin 15) := rfl
  have hs6 : Fin.succ (6 : Fin 14)=(7 : Fin 15) := rfl
  have hs7 : Fin.succ (7 : Fin 14)=(8 : Fin 15) := rfl
  have hs8 : Fin.succ (8 : Fin 14)=(9 : Fin 15) := rfl
  have hs9 : Fin.succ (9 : Fin 14)=(10 : Fin 15) := rfl
  have hs10 : Fin.succ (10 : Fin 14)=(11 : Fin 15) := rfl
  have hs11 : Fin.succ (11 : Fin 14)=(12 : Fin 15) := rfl
  have hs12 : Fin.succ (12 : Fin 14)=(13 : Fin 15) := rfl
  have hs13 : Fin.succ (13 : Fin 14)=(14 : Fin 15) := rfl
  have h₂ := (WebBoundary.Family.local_relations hm).2.2.1
  have h₆ := (WebBoundary.Family.local_relations hm).2.2.2.2.2.2.1
  simp only [Program.raw,familyProgram,Program.linear,Event.linear,familyEvent,
    familyTrace,List.get,Path.raw,WebEvaluationCompression.Resolution.finePath,
    Path.linear,familyResolution,LinearMap.comp_apply,LinearMap.id_apply]
  iterate 5
    apply merge_value_congr K D L
    · simp only [stateIndex_family hm,hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,h₂,h₆,WebBoundary.Family.idx_source,
        WebBoundary.Family.idx_output,WebBoundary.Family.idx_cyclic,
        WebBoundary.Family.idx_common,WebBoundary.Family.idx_middle,
        WebBoundary.Family.idx_common_again,WebBoundary.Family.idx_output_again]
    · simp only [stateIndex_family hm,hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,h₂,h₆,WebBoundary.Family.idx_source,
        WebBoundary.Family.idx_output,WebBoundary.Family.idx_cyclic,
        WebBoundary.Family.idx_common,WebBoundary.Family.idx_middle,
        WebBoundary.Family.idx_common_again,WebBoundary.Family.idx_output_again]
    try simp only [WebEvaluation.split_val,reframe_val]
  simp only [SphericalMaps.generator_val,mul_one,stateIndex_family hm,
    WebBoundary.Family.idx_source]

/-- The specific graph-evaluation bridge missing from the earlier audit.
The graph presentation is constructed by actual replay, and the equality
is proved by local map composition and binary-resolution independence. -/
theorem family_graph_evaluation_eq_raw :
    (familyPresentedGraph hm).evaluate (show 0<2*m+1 by omega) K D L=
      ParabolicWeb.Family.raw K D L := by
  change (familyProgram hm).raw _ K D L=ParabolicWeb.Family.raw K D L
  rw [familyProgram_raw_eq_fine,
    WebEvaluationCompression.Resolution.fine_raw_eq_coarse,
    familyResolution_coarse,WebEvaluation.Family.raw_eq]

end Guralnick.WebTraceEvaluation
