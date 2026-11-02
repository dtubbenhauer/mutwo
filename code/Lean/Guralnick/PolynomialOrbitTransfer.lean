import Guralnick.PolynomialOrbitCoordinates
import Guralnick.LatticeEquivariance

/-!
# Transport of the periodic orbit-coordinate theorem

Only the independent polynomial cut-coordinate statement is supplied as
literature input. The completed arbitrary-basis statement is derived by
natural completion and an actual Laurent-linear quotient equivalence.
-/
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace Guralnick.PolynomialOrbitCoordinates
open LatticeGallery
variable (k : Type) [Field k] (N : ℕ) [NeZero N]

/-- Change of basis on the target cut, at the level of actual subspaces. -/
theorem target_chart (g : LaurentLattice.Ambient k N ≃ₗ[LaurentSeries k] LaurentLattice.Ambient k N)
    (a : ℤ) : (completedTarget k N a).map (g.restrictScalars k).toLinearMap =
      OrbitMatrix.targetCut k N g a := rfl

/-- Change of basis on the window-translated source cut. -/
theorem source_chart (g : LaurentLattice.Ambient k N ≃ₗ[LaurentSeries k] LaurentLattice.Ambient k N)
    (w : AffinePermutation N) (a : ℤ) :
    (completedSource k N w a).map (g.restrictScalars k).toLinearMap =
      OrbitMatrix.sourceCut k N g w a := by
  unfold OrbitMatrix.sourceCut
  rw [AffineLatticePosition.mapModule_trans]
  rfl

/-- The coordinate change acts on the actual block quotient. -/
def chartBlockEquiv
    (g : LaurentLattice.Ambient k N ≃ₗ[LaurentSeries k] LaurentLattice.Ambient k N)
    (w : AffinePermutation N) (a b c d : ℤ) :
    CompletedBlockQuotient k N w a b c d ≃ₗ[k] OrbitMatrix.BlockQuotient k N g w a b c d := by
  let A := (completedTarget k N a ⊓ completedSource k N w d) ⊔
    (completedTarget k N b ⊓ completedSource k N w c)
  let B := completedTarget k N b ⊓ completedSource k N w d
  have hA : A.map (g.restrictScalars k).toLinearMap =
      (OrbitMatrix.targetCut k N g a ⊓ OrbitMatrix.sourceCut k N g w d) ⊔
        (OrbitMatrix.targetCut k N g b ⊓ OrbitMatrix.sourceCut k N g w c) := by
    simp only [A,LatticeEquivariance.subspace_map_sup,LatticeEquivariance.subspace_map_inf,
      target_chart,source_chart]
  have hB : B.map (g.restrictScalars k).toLinearMap =
      OrbitMatrix.targetCut k N g b ⊓ OrbitMatrix.sourceCut k N g w d := by
    simp only [B,LatticeEquivariance.subspace_map_inf,target_chart,source_chart]
  exact (LatticeEquivariance.subspaceQuotientEquiv g A B).trans (quotientCongr k hA hB)

/-- The same change of basis acts on the cumulative quotient. -/
def chartCumulativeEquiv
    (g : LaurentLattice.Ambient k N ≃ₗ[LaurentSeries k] LaurentLattice.Ambient k N)
    (w : AffinePermutation N) (a b c : ℤ) :
    CompletedCumulativeQuotient k N w a b c ≃ₗ[k] OrbitMatrix.CumulativeQuotient k N g w a b c := by
  let A := completedTarget k N a
  let B := completedTarget k N b ⊓ (completedSource k N w c ⊔ completedTarget k N a)
  have hA : A.map (g.restrictScalars k).toLinearMap = OrbitMatrix.targetCut k N g a :=
    target_chart k N g a
  have hB : B.map (g.restrictScalars k).toLinearMap = OrbitMatrix.targetCut k N g b ⊓
      (OrbitMatrix.sourceCut k N g w c ⊔ OrbitMatrix.targetCut k N g a) := by
    simp only [B,LatticeEquivariance.subspace_map_sup,LatticeEquivariance.subspace_map_inf,
      target_chart,source_chart]
  exact (LatticeEquivariance.subspaceQuotientEquiv g A B).trans (quotientCongr k hA hB)

def blockCompletionEquiv
    (g : LaurentLattice.Ambient k N ≃ₗ[LaurentSeries k] LaurentLattice.Ambient k N)
    (w : AffinePermutation N) (a b c d : ℤ) :
    BlockQuotient k N w a b c d ≃ₗ[k] OrbitMatrix.BlockQuotient k N g w a b c d :=
  (blockEquiv k N w a b c d).trans (chartBlockEquiv k N g w a b c d)

def cumulativeCompletionEquiv
    (g : LaurentLattice.Ambient k N ≃ₗ[LaurentSeries k] LaurentLattice.Ambient k N)
    (w : AffinePermutation N) (a b c : ℤ) :
    CumulativeQuotient k N w a b c ≃ₗ[k] OrbitMatrix.CumulativeQuotient k N g w a b c :=
  (cumulativeEquiv k N w a b c).trans (chartCumulativeEquiv k N g w a b c)

theorem completed_source_le_target (w : AffinePermutation N) (a b : ℤ) :
    completedSource k N w b ≤ completedTarget k N a ↔ sourceCut k N w b ≤ targetCut k N a := by
  rw [← complete_source,← complete_target]
  change LatticeCompletion.orderIso (sourceLattice k N w b) ≤
      LatticeCompletion.orderIso (cutLattice k N a) ↔ _
  exact LatticeCompletion.orderIso.map_rel_iff

theorem completed_target_le_source (w : AffinePermutation N) (a b : ℤ) :
    completedTarget k N a ≤ completedSource k N w b ↔ targetCut k N a ≤ sourceCut k N w b := by
  rw [← complete_source,← complete_target]
  change LatticeCompletion.orderIso (cutLattice k N a) ≤
      LatticeCompletion.orderIso (sourceLattice k N w b) ↔ _
  exact LatticeCompletion.orderIso.map_rel_iff

/-- All six completed orbit-coordinate fields follow from the polynomial
coordinate theorem. No model-comparison field remains. -/
def Input.toCompleted (C : Input k N) : OrbitMatrix.CoordinateDimensionInput k N where
  block_finite := by
    intro g w a b c d hab hcd
    letI := block_finite k N w a b c d
    exact (blockCompletionEquiv k N g w a b c d).finiteDimensional
  block_dimension := by
    intro g w a b c d hab hcd
    rw [← (blockCompletionEquiv k N g w a b c d).finrank_eq]
    exact C.block_dimension w a b c d hab hcd
  cumulative_finite := by
    intro g w a b c hab
    letI := cumulative_finite k N w a b c
    exact (cumulativeCompletionEquiv k N g w a b c).finiteDimensional
  cumulative_dimension := by
    intro g w a b c hab
    rw [← (cumulativeCompletionEquiv k N g w a b c).finrank_eq]
    exact C.cumulative_dimension w a b c hab
  source_le_target := by
    intro g w a b
    rw [← source_chart,← target_chart,
      Submodule.map_le_map_iff_of_injective (f := (g.restrictScalars k).toLinearMap)
        (g.restrictScalars k).injective,completed_source_le_target]
    exact C.source_le_target w a b
  target_le_source := by
    intro g w a b
    rw [← source_chart,← target_chart,
      Submodule.map_le_map_iff_of_injective (f := (g.restrictScalars k).toLinearMap)
        (g.restrictScalars k).injective,completed_target_le_source]
    exact C.target_le_source w a b

#print axioms blockCompletionEquiv
#print axioms cumulativeCompletionEquiv
#print axioms Input.toCompleted
end Guralnick.PolynomialOrbitCoordinates
