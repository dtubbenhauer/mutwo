import Guralnick.WebFamilyEvaluation
import Guralnick.WebRightLinearity
import Guralnick.WebPresentedWinding
import Guralnick.WebRecutPositions
import Guralnick.WebLiterature

/-!
# The actual graph in the canonical-basis proof

The evaluated graph is identified with the raw element before transferring
any standard or canonical coefficients. The same correction is then applied
to that graph evaluation, and its fixed-source critical coefficient is
proved uniformly. No extra diagram-identification hypothesis is introduced.
-/
noncomputable section
open scoped BigOperators
namespace Guralnick.WebProof

variable {m : ℕ} (hm : 2≤m) (T : Hecke.Theory (2*m+1)) (W : WebLiterature T)

/-- Evaluation of the original graph with its checked ordered presentation. -/
def graphRaw : Hecke.Algebra (2*m+1) :=
  (WebTraceEvaluation.familyPresentedGraph hm).evaluate (show 0<2*m+1 by omega)
    T.kl W.longest W.parabolic

theorem graph_raw_eq : graphRaw hm T W=W.raw :=
  WebTraceEvaluation.family_graph_evaluation_eq_raw hm T.kl W.longest W.parabolic

/-- The input chart is the prescribed finite spherical source. -/
theorem graph_source_chart :
    WebTraceEvaluation.stateIndex (show 0<2*m+1 by omega) (WebTrace.familyState m 0)=
      ParabolicWeb.Family.source m :=
  (WebTraceEvaluation.stateIndex_family hm 0).trans (WebBoundary.Family.idx_source hm)

theorem graph_target_chart :
    WebTraceEvaluation.stateIndex (show 0<2*m+1 by omega) (WebTrace.familyState m 14)=
      ParabolicWeb.Family.output m :=
  (WebTraceEvaluation.stateIndex_family hm 14).trans (WebBoundary.Family.idx_output_again hm)

/-- The full interpreted graph morphism, with its endpoint charts identified
with the manuscript's source and output right Hecke modules. -/
def graphMorphism :
    WebEvaluation.ModuleAt T.kl W.longest (ParabolicWeb.Family.source m) →ₗ[Hecke.R]
      WebEvaluation.ModuleAt T.kl W.longest (ParabolicWeb.Family.output m) :=
  (WebTraceEvaluation.reframe T.kl W.longest (graph_target_chart hm)).comp
    (((WebTraceEvaluation.familyProgram hm).linear (show 0<2*m+1 by omega)
      T.kl W.longest W.parabolic).comp
      (WebTraceEvaluation.reframe T.kl W.longest (graph_source_chart hm).symm))

theorem graph_morphism_rightLinear : WebRightLinearity.RightLinear (graphMorphism hm T W) := by
  apply WebRightLinearity.comp_rightLinear
  · apply WebRightLinearity.comp_rightLinear
    · exact WebRightLinearity.reframe_rightLinear T.kl W.longest _
    · exact WebRightLinearity.program_rightLinear _ T.kl W.longest W.parabolic _
  · exact WebRightLinearity.reframe_rightLinear T.kl W.longest _

theorem graph_morphism_generator :
    (graphMorphism hm T W (SphericalMaps.generator
      (ParabolicWeb.symmetrizer T.kl W.longest (ParabolicWeb.Family.source m)) 1)).val=
        graphRaw hm T W := by
  unfold graphMorphism
  rw [LinearMap.comp_apply,LinearMap.comp_apply,WebTraceEvaluation.reframe_val]
  have he : WebTraceEvaluation.reframe T.kl W.longest (graph_source_chart hm).symm
      (SphericalMaps.generator
        (ParabolicWeb.symmetrizer T.kl W.longest (ParabolicWeb.Family.source m)) 1)=
      SphericalMaps.generator (ParabolicWeb.symmetrizer T.kl W.longest
        (WebTraceEvaluation.stateIndex (show 0<2*m+1 by omega) (WebTrace.familyState m 0))) 1 := by
    apply Subtype.ext
    rw [WebTraceEvaluation.reframe_val]
    simp only [SphericalMaps.generator_val,graph_source_chart hm]
  rw [he]
  rfl

/-- Equality of the entire right Hecke-module morphism, not only its value
at the generator or a selected standard coefficient. -/
theorem graph_morphism_eq_sixMaps :
    graphMorphism hm T W=(ParabolicWeb.Family.sixMaps T.kl W.longest W.parabolic).linear := by
  apply WebRightLinearity.ext_generator _ _ (graph_morphism_rightLinear hm T W)
  · rw [←WebEvaluation.Family.linear_eq_sixMaps T.kl W.longest W.parabolic]
    exact WebRightLinearity.path_rightLinear T.kl W.longest W.parabolic _
  · rw [graph_morphism_generator,graph_raw_eq]
    rfl

/-- Every standard coordinate computed in the original proof is a
coordinate of the actual graph evaluation. -/
theorem graph_standard_coordinates :
    T.kl.standard.repr (graphRaw hm T W)=T.kl.standard.repr W.raw := by
  rw [graph_raw_eq]

/-- The bridge identifies the whole canonical expansion, not just one
numeric coefficient or the support of a matrix encoding. -/
theorem graph_canonical_coordinates :
    T.kl.canonical.repr (graphRaw hm T W)=T.kl.canonical.repr W.raw := by
  rw [graph_raw_eq]

/-- The manuscript's correction applied to the evaluated concrete graph. -/
def graphCorrected : Hecke.Algebra (2*m+1) :=
  graphRaw hm T W-∑ r ∈ Finset.range (m-1),
    CanonicalCorrection.correction (m-r) • T.kl.canonical (CanonicalSpherical.index m r)

theorem graph_corrected_eq :
    graphCorrected hm T W=CanonicalRowSum.corrected T.kl W.longest W.parabolic
      (CanonicalSpherical.index m) := by
  unfold graphCorrected CanonicalRowSum.corrected
  rw [graph_raw_eq]

/-- The corrected actual graph has exactly the already-proved Gaussian
residual at the required fixed trivial-source standard. -/
theorem graph_corrected_source :
    T.kl.standard.repr (graphCorrected hm T W) (AffinePermutation.longest (2*m+1))=
      CanonicalFullCorrection.residual CanonicalCorrection.correction m := by
  rw [graph_corrected_eq]
  apply CanonicalRowSum.corrected_source_coordinate
  · simpa only [CanonicalSpherical.index_zero,Nat.sub_zero] using
      WebLiterature.full_coordinate hm T W 0 (by omega)
  · intro r hr
    simpa only [CanonicalSpherical.index_zero,Nat.sub_zero,Nat.zero_le,if_true] using
      WebLiterature.full_transition hm T W r 0 (by omega) (by omega)

/-- Critical readout directly on the corrected graph evaluation. -/
theorem graph_corrected_critical :
    T.kl.standard.repr (graphCorrected hm T W) (AffinePermutation.longest (2*m+1)) 1=
      (Nat.choose (m+1) 2 : ℤ) := by
  rw [graph_corrected_source]
  exact CanonicalFullCorrection.corrected_critical hm

end Guralnick.WebProof
