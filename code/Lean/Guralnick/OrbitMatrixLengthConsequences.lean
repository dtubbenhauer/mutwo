import Guralnick.OrbitMatrixInjectivity
import Guralnick.FiniteDoubleCosetMaximum

/-!
# Elementary consequences of the orbit-dimension identity

This intermediate API takes the dimension/length identity as a parameter.
`OrbitDimensionLength` now proves it from actual inversion sums, so it is
not a final literature input. Matrix injectivity is proved by sorted monomials.
Its maximality converse follows by maximizing length inside the actual
finite double coset and checking that its supported matrix is unchanged.
-/
noncomputable section
namespace Guralnick.OrbitMatrixElementary
open Hecke ParabolicWeb CanonicalSchur
variable {N : ℕ} [NeZero N]

/-- The periodic dimension identity, proved in `OrbitDimensionLength`. -/
def DimensionLengthInput (c : WindowCoxeter N) : Prop :=
  ∀ (A : FiniteBlocks.Composition N), A.cut.val=0 →
    ∀ (w : AffinePermutation N), WindowPacketMatrix.Supported w →
      DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) w →
      PeriodicMatrix.dimension (fun i j => (OrbitMatrix.compositionEntries A w i j : ℤ)) =
        (c.system.length w : ℤ)-c.system.length (AffinePermutation.longest N)

/-- Equality with the orbit's maximal length forces actual descent maximality.
The separate right-descent premise of the former input is unnecessary. -/
theorem maximal_of_dimension (c : WindowCoxeter N) (H : DimensionLengthInput c)
    (A : FiniteBlocks.Composition N) (hA : A.cut.val=0) (w : AffinePermutation N)
    (hw : WindowPacketMatrix.Supported w)
    (hd : (c.system.length w : ℤ)-c.system.length (AffinePermutation.longest N) =
      PeriodicMatrix.dimension (fun i j => (OrbitMatrix.compositionEntries A w i j : ℤ))) :
    DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) w := by
  obtain ⟨z,⟨a,b,rfl⟩,hmax,hbound⟩ := FiniteDoubleCosetMaximum.exists_maximum c A.index
    (CanonicalChains.source (NeZero.pos N))
    (ElementaryCoxeterParabolic.longestData c A.index)
    (ElementaryCoxeterParabolic.longestData c (CanonicalChains.source (NeZero.pos N))) w
  have hz := H A hA (a.val*w*b.val) (supported_double_action c A hA a b w hw) hmax
  rw [entries_double_action c A hA a b w] at hz
  have hlen : c.system.length (a.val*w*b.val) = c.system.length w := by omega
  apply FiniteDoubleCosetMaximum.doubleMaximal_of_bound
  intro a' b'
  simpa only [hlen] using hbound a' b'

/-- Derive the old three-clause interface from the dimension identity. -/
def toThreeColumnLengthInput (c : WindowCoxeter N) (H : DimensionLengthInput c) :
    OrbitMatrix.ThreeColumnLengthInput c where
  dimension_length := H
  maximal_of_dimension A hA w hw _ hd := maximal_of_dimension c H A hA w hw hd
  matrix_injective := matrix_injective c

#print axioms matrix_injective
#print axioms maximal_of_dimension
#print axioms toThreeColumnLengthInput
end Guralnick.OrbitMatrixElementary
