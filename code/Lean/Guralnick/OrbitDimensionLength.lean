import Guralnick.OrbitDimensionLabels
import Guralnick.OrbitDimensionPairs
import Guralnick.OrbitDimensionHistogram
import Guralnick.OrbitMatrixLengthConsequences

/-!
# The supported matrix dimension/length identity is elementary

Both sides are sums over actual residue pairs. The matrix histogram
expansion, decreasing source window, and decreasing winding inside output
packets identify the summands. Thus the former dimension input is derived
from the actual affine permutation model, without an orbit theorem.
-/
noncomputable section
namespace Guralnick.OrbitDimensionLength
open Hecke CanonicalSchur OrbitDimensionLabels OrbitDimensionInversions
open OrbitDimensionPairs OrbitDimensionHistogram
open scoped BigOperators
variable {N : ℕ} [NeZero N]

/-- The generic supported matrix dimension formula follows from inversion
counting for every positive output composition and maximal endpoint. -/
theorem dimensionLength (c : WindowCoxeter N) :
    OrbitMatrixElementary.DimensionLengthInput c := by
  intro A hA w hs hw
  rw [length_gap c w hw.2 hs]
  simp_rw [compositionEntries_eq A w hs]
  change PeriodicMatrix.dimension
    (fun r d => (histogram (row A) (col w hs) r d : ℤ)) = _
  rw [dimension_histogram]
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N,
        ((if (w⁻¹).winding i+1 < (w⁻¹).winding j then (1 : ℤ) else 0)+
          (if row A j ≤ row A i ∧ (w⁻¹).winding i < (w⁻¹).winding j then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hi := col_val w hs i
      have hj := col_val w hs j
      have h₁ : (col w hs i).val+1 < (col w hs j).val ↔
          (w⁻¹).winding i+1 < (w⁻¹).winding j := by omega
      have h₂ : col w hs i < col w hs j ↔
          (w⁻¹).winding i < (w⁻¹).winding j := by
        change (col w hs i).val < (col w hs j).val ↔ _
        omega
      simp only [h₁,h₂]
    _ = _ := matrix_pair_sum (row A) (w⁻¹).winding (row_monotone A)
      (winding_antitone_on_rows c A hA w hw.1)

/-- All clauses of the former orbit-matrix interface are now proved. -/
def threeColumnLength (c : WindowCoxeter N) : OrbitMatrix.ThreeColumnLengthInput c :=
  OrbitMatrixElementary.toThreeColumnLengthInput c (dimensionLength c)

#print axioms dimensionLength
#print axioms threeColumnLength
end Guralnick.OrbitDimensionLength
