import Guralnick.PolynomialOrbitCuts
import Guralnick.CoordinateSubspaceQuotient

/-!
# The four periodic-coordinate formulas, proved from actual monomials

The block and cumulative quotient dimensions are the cardinalities of
finite differences of basis-index sets. Containment is literal inclusion
of those sets. No periodic-coordinate theorem is supplied as an input.
-/
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace Guralnick.PolynomialOrbitCounting
open PolynomialOrbitCoordinates CoordinateSubspace LatticeGallery
variable (k : Type) [Field k] (N : ℕ) [NeZero N]

theorem targetCut_spanSet (a : ℤ) :
    targetCut k N a = spanSet (integerBasis k N) {z : ℤ | z ≤ a} :=
  targetCut_span k N a

theorem sourceCut_spanSet (w : AffinePermutation N) (a : ℤ) :
    sourceCut k N w a = spanSet (integerBasis k N) {z : ℤ | w.onIntegers.symm z ≤ a} :=
  sourceCut_span k N w a

/-- The actual block quotient has one basis vector for each surviving
integer in the literal row/window interval intersection. -/
theorem block_dimension (w : AffinePermutation N) (a b c d : ℤ) :
    Module.finrank k (BlockQuotient k N w a b c d) = OrbitMatrix.blockCount N w a b c d := by
  classical
  let e := integerBasis k N
  let A : Set ℤ := ({z | z ≤ a} ∩ {z | w.onIntegers.symm z ≤ d}) ∪
    ({z | z ≤ b} ∩ {z | w.onIntegers.symm z ≤ c})
  let B : Set ℤ := {z | z ≤ b} ∩ {z | w.onIntegers.symm z ≤ d}
  have hA : (targetCut k N a ⊓ sourceCut k N w d) ⊔
      (targetCut k N b ⊓ sourceCut k N w c) = spanSet e A := by
    simp only [targetCut_spanSet,sourceCut_spanSet,spanSet_inf,spanSet_sup,e,A]
  have hB : targetCut k N b ⊓ sourceCut k N w d = spanSet e B := by
    simp only [targetCut_spanSet,sourceCut_spanSet,spanSet_inf,e,B]
  let E : BlockQuotient k N w a b c d ≃ₗ[k] QuotientSpace (spanSet e A) (spanSet e B) :=
    quotientCongr k hA hB
  have hs : B \ A = (((Finset.Ioc a b).filter
      (fun z => c < w.onIntegers.symm z ∧ w.onIntegers.symm z ≤ d)) : Set ℤ) := by
    ext z
    simp only [A,B,Set.mem_diff,Set.mem_inter_iff,Set.mem_union,Set.mem_setOf_eq,
      Finset.mem_coe,Finset.mem_filter,Finset.mem_Ioc]
    omega
  exact E.finrank_eq.trans (quotient_finrank e A B _ hs)

/-- Cumulative dimensions count exactly the row labels above the lower
row cut whose inverse window labels remain below the source cut. -/
theorem cumulative_dimension (w : AffinePermutation N) (a b c : ℤ) :
    Module.finrank k (CumulativeQuotient k N w a b c) = OrbitMatrix.cumulativeCount N w a b c := by
  classical
  let e := integerBasis k N
  let A : Set ℤ := {z | z ≤ a}
  let B : Set ℤ := {z | z ≤ b} ∩ ({z | w.onIntegers.symm z ≤ c} ∪ {z | z ≤ a})
  have hA : targetCut k N a = spanSet e A := targetCut_spanSet k N a
  have hB : targetCut k N b ⊓ (sourceCut k N w c ⊔ targetCut k N a) = spanSet e B := by
    simp only [targetCut_spanSet,sourceCut_spanSet,spanSet_inf,spanSet_sup,e,B]
  let E : CumulativeQuotient k N w a b c ≃ₗ[k] QuotientSpace (spanSet e A) (spanSet e B) :=
    quotientCongr k hA hB
  have hs : B \ A = (((Finset.Ioc a b).filter
      (fun z => w.onIntegers.symm z ≤ c)) : Set ℤ) := by
    ext z
    simp only [A,B,Set.mem_diff,Set.mem_inter_iff,Set.mem_union,Set.mem_setOf_eq,
      Finset.mem_coe,Finset.mem_filter,Finset.mem_Ioc]
    omega
  exact E.finrank_eq.trans (quotient_finrank e A B _ hs)

theorem source_le_target (w : AffinePermutation N) (a b : ℤ) :
    sourceCut k N w b ≤ targetCut k N a ↔ ∀ i : ℤ, i ≤ b → w.onIntegers i ≤ a := by
  rw [sourceCut_spanSet,targetCut_spanSet,spanSet_le_iff]
  constructor
  · intro h i hi
    apply h
    simpa using hi
  · intro h z hz
    have he := h (w.onIntegers.symm z) hz
    simpa using he

theorem target_le_source (w : AffinePermutation N) (a b : ℤ) :
    targetCut k N a ≤ sourceCut k N w b ↔ ∀ i : ℤ, i ≤ a → w.onIntegers.symm i ≤ b := by
  rw [sourceCut_spanSet,targetCut_spanSet,spanSet_le_iff]
  rfl

/-- All four former coordinate inputs are theorems about the independently
defined polynomial modules and the actual affine permutation. -/
def provedInput : PolynomialOrbitCoordinates.Input k N where
  block_dimension w a b c d _ _ := block_dimension k N w a b c d
  cumulative_dimension w a b c _ := cumulative_dimension k N w a b c
  source_le_target := source_le_target k N
  target_le_source := target_le_source k N

#print axioms block_dimension
#print axioms cumulative_dimension
#print axioms source_le_target
#print axioms target_le_source
#print axioms provedInput
end Guralnick.PolynomialOrbitCounting
