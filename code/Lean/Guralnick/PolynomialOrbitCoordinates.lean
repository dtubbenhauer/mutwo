import Guralnick.PolynomialAffineCoordinates
import Guralnick.PolynomialLatticeOperations
import Guralnick.OrbitMatrix

/-!
# Polynomial periodic cut lattices and coordinate quotients

These are the ordinary polynomial-Laurent cut modules and their actual
intersection/sum quotients. Completion preserves each module operation and
induces actual linear equivalences of the displayed coordinate quotients.
-/
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace Guralnick.PolynomialOrbitCoordinates
open PolynomialLattice PolynomialAffineCoordinates LatticeGallery
open scoped BigOperators
variable (k : Type) [Field k] (N : ℕ) [NeZero N]

def cutModule (a : ℤ) : Submodule (Polynomial k) (PolynomialLattice.Ambient k N) :=
  Submodule.span (Polynomial k) (Set.range fun i : Fin N =>
    PolynomialAffineCoordinates.coordinateVector k N i (OrbitMatrix.cutLevel N a i))

def cutLattice (a : ℤ) : PolynomialLattice.Lattice k N where
  module := cutModule k N a
  finite := Submodule.fg_span (Set.finite_range _)
  spanning := by
    classical
    apply top_unique
    intro x _
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _
    let q := OrbitMatrix.cutLevel N a i
    have hgen : PolynomialAffineCoordinates.coordinateVector k N i q ∈ cutModule k N a :=
      Submodule.subset_span ⟨i,rfl⟩
    have hspan := Submodule.subset_span (R := LaurentPolynomial k) hgen
    have hmul := (Submodule.span (LaurentPolynomial k)
      (cutModule k N a : Set (PolynomialLattice.Ambient k N))).smul_mem
      (x i * PolynomialAffineCoordinates.monomial k q) hspan
    have he : (x i * PolynomialAffineCoordinates.monomial k q) •
        PolynomialAffineCoordinates.coordinateVector k N i q = Pi.single i (x i) := by
      funext j
      by_cases h : i = j
      · subst j
        simp only [PolynomialAffineCoordinates.coordinateVector,Pi.smul_apply,Pi.single_eq_same,
          smul_eq_mul,mul_assoc,PolynomialAffineCoordinates.monomial_mul,add_neg_cancel,
          PolynomialAffineCoordinates.monomial_zero,mul_one]
      · simp [PolynomialAffineCoordinates.coordinateVector,h]
    rwa [he] at hmul

def sourceLattice (w : AffinePermutation N) (a : ℤ) : PolynomialLattice.Lattice k N :=
  PolynomialAffineCoordinates.mapLattice k N (PolynomialAffineCoordinates.windowEquiv k N w)
    (cutLattice k N a)

def targetCut (a : ℤ) : Submodule k (PolynomialLattice.Ambient k N) := (cutLattice k N a).space
def sourceCut (w : AffinePermutation N) (a : ℤ) : Submodule k (PolynomialLattice.Ambient k N) :=
  (sourceLattice k N w a).space

def completedTarget (a : ℤ) : Submodule k (LaurentLattice.Ambient k N) :=
  (OrbitMatrix.cutModule k N a).restrictScalars k

def completedSource (w : AffinePermutation N) (a : ℤ) : Submodule k (LaurentLattice.Ambient k N) :=
  (AffineLatticePosition.mapModule k N (AffineLatticePosition.windowEquiv k N w)
    (OrbitMatrix.cutModule k N a)).restrictScalars k

theorem complete_cutModule (a : ℤ) : LatticeCompletion.completeModule (cutModule k N a) =
    OrbitMatrix.cutModule k N a := by
  rw [cutModule,LatticeCompletion.complete_span_range]
  simp only [PolynomialAffineCoordinates.inclusion_coordinateVector,OrbitMatrix.cutModule]

theorem complete_target (a : ℤ) :
    (LatticeCompletion.complete (cutLattice k N a)).space = completedTarget k N a := by
  change (LatticeCompletion.completeModule (cutModule k N a)).restrictScalars k = _
  rw [complete_cutModule]
  rfl

theorem complete_source (w : AffinePermutation N) (a : ℤ) :
    (LatticeCompletion.complete (sourceLattice k N w a)).space = completedSource k N w a := by
  change (LatticeCompletion.completeModule
    (PolynomialAffineCoordinates.mapModule k N (PolynomialAffineCoordinates.windowEquiv k N w)
      (cutModule k N a))).restrictScalars k = _
  rw [PolynomialAffineCoordinates.complete_windowModule,complete_cutModule]
  rfl

abbrev BlockQuotient (w : AffinePermutation N) (a b c d : ℤ) :=
  QuotientSpace
    ((targetCut k N a ⊓ sourceCut k N w d) ⊔ (targetCut k N b ⊓ sourceCut k N w c))
    (targetCut k N b ⊓ sourceCut k N w d)

abbrev CumulativeQuotient (w : AffinePermutation N) (a b c : ℤ) :=
  QuotientSpace (targetCut k N a)
    (targetCut k N b ⊓ (sourceCut k N w c ⊔ targetCut k N a))

abbrev CompletedBlockQuotient (w : AffinePermutation N) (a b c d : ℤ) :=
  QuotientSpace
    ((completedTarget k N a ⊓ completedSource k N w d) ⊔
      (completedTarget k N b ⊓ completedSource k N w c))
    (completedTarget k N b ⊓ completedSource k N w d)

abbrev CompletedCumulativeQuotient (w : AffinePermutation N) (a b c : ℤ) :=
  QuotientSpace (completedTarget k N a)
    (completedTarget k N b ⊓ (completedSource k N w c ⊔ completedTarget k N a))

/-- Equality of ambient subspaces gives the corresponding actual quotient equivalence. -/
def quotientCongr {V : Type} [AddCommGroup V] [Module k V]
    {A B C D : Submodule k V} (hA : A = C) (hB : B = D) :
    QuotientSpace A B ≃ₗ[k] QuotientSpace C D := by
  subst C; subst D
  exact LinearEquiv.refl _ _

/-- The actual polynomial block quotient and its completed block quotient agree. -/
def blockEquiv (w : AffinePermutation N) (a b c d : ℤ) :
    BlockQuotient k N w a b c d ≃ₗ[k] CompletedBlockQuotient k N w a b c d := by
  let A := PolynomialLattice.sumLattice
    (PolynomialLattice.interLattice (cutLattice k N a) (sourceLattice k N w d))
    (PolynomialLattice.interLattice (cutLattice k N b) (sourceLattice k N w c))
  let B := PolynomialLattice.interLattice (cutLattice k N b) (sourceLattice k N w d)
  have hA : A.space = (targetCut k N a ⊓ sourceCut k N w d) ⊔
      (targetCut k N b ⊓ sourceCut k N w c) := by simp [A,targetCut,sourceCut]
  have hB : B.space = targetCut k N b ⊓ sourceCut k N w d := rfl
  have hCA : (LatticeCompletion.complete A).space =
      (completedTarget k N a ⊓ completedSource k N w d) ⊔
        (completedTarget k N b ⊓ completedSource k N w c) := by
    simp only [A,LatticeCompletion.complete_sum_space,LatticeCompletion.complete_inter_space,
      complete_target,complete_source]
  have hCB : (LatticeCompletion.complete B).space =
      completedTarget k N b ⊓ completedSource k N w d := by
    simp only [B,LatticeCompletion.complete_inter_space,complete_target,complete_source]
  exact (quotientCongr k hA.symm hB.symm).trans
    ((LatticeCompletion.quotientEquiv A B).trans (quotientCongr k hCA hCB))

/-- The same comparison for cumulative intersection quotients. -/
def cumulativeEquiv (w : AffinePermutation N) (a b c : ℤ) :
    CumulativeQuotient k N w a b c ≃ₗ[k] CompletedCumulativeQuotient k N w a b c := by
  let A := cutLattice k N a
  let B := PolynomialLattice.interLattice (cutLattice k N b)
    (PolynomialLattice.sumLattice (sourceLattice k N w c) (cutLattice k N a))
  have hB : B.space = targetCut k N b ⊓ (sourceCut k N w c ⊔ targetCut k N a) := by
    simp [B,targetCut,sourceCut]
  have hCB : (LatticeCompletion.complete B).space = completedTarget k N b ⊓
      (completedSource k N w c ⊔ completedTarget k N a) := by
    simp only [B,LatticeCompletion.complete_sum_space,LatticeCompletion.complete_inter_space,
      complete_target,complete_source]
  exact (quotientCongr k rfl hB.symm).trans
    ((LatticeCompletion.quotientEquiv A B).trans (quotientCongr k (complete_target k N a) hCB))

/-- Finiteness follows from the actual polynomial lattice bounds. -/
theorem block_finite (w : AffinePermutation N) (a b c d : ℤ) :
    FiniteDimensional k (BlockQuotient k N w a b c d) := by
  let A := PolynomialLattice.sumLattice
    (PolynomialLattice.interLattice (cutLattice k N a) (sourceLattice k N w d))
    (PolynomialLattice.interLattice (cutLattice k N b) (sourceLattice k N w c))
  let B := PolynomialLattice.interLattice (cutLattice k N b) (sourceLattice k N w d)
  have hA : A.space = (targetCut k N a ⊓ sourceCut k N w d) ⊔
      (targetCut k N b ⊓ sourceCut k N w c) := by simp [A,targetCut,sourceCut]
  have hB : B.space = targetCut k N b ⊓ sourceCut k N w d := rfl
  letI := LatticeCompletion.quotient_finite A B
  exact (quotientCongr k hA hB).finiteDimensional

/-- Cumulative quotients are finite-dimensional without invoking the
coordinate counting formula. -/
theorem cumulative_finite (w : AffinePermutation N) (a b c : ℤ) :
    FiniteDimensional k (CumulativeQuotient k N w a b c) := by
  let A := cutLattice k N a
  let B := PolynomialLattice.interLattice (cutLattice k N b)
    (PolynomialLattice.sumLattice (sourceLattice k N w c) (cutLattice k N a))
  have hB : B.space = targetCut k N b ⊓ (sourceCut k N w c ⊔ targetCut k N a) := by
    simp [B,targetCut,sourceCut]
  letI := LatticeCompletion.quotient_finite A B
  exact (quotientCongr k (show A.space = targetCut k N a from rfl) hB).finiteDimensional

/-- Standard periodic polynomial-coordinate facts, with no completion or
arbitrary Laurent-series basis change hidden in the input. -/
structure Input : Prop where
  block_dimension : ∀ (w : AffinePermutation N) (a b c d : ℤ), a ≤ b → c ≤ d →
    Module.finrank k (BlockQuotient k N w a b c d) = OrbitMatrix.blockCount N w a b c d
  cumulative_dimension : ∀ (w : AffinePermutation N) (a b c : ℤ), a ≤ b →
    Module.finrank k (CumulativeQuotient k N w a b c) = OrbitMatrix.cumulativeCount N w a b c
  source_le_target : ∀ (w : AffinePermutation N) (a b : ℤ),
    sourceCut k N w b ≤ targetCut k N a ↔ ∀ i : ℤ, i ≤ b → w.onIntegers i ≤ a
  target_le_source : ∀ (w : AffinePermutation N) (a b : ℤ),
    targetCut k N a ≤ sourceCut k N w b ↔ ∀ i : ℤ, i ≤ a → w.onIntegers.symm i ≤ b

#print axioms block_finite
#print axioms cumulative_finite
#print axioms blockEquiv
#print axioms cumulativeEquiv
end Guralnick.PolynomialOrbitCoordinates
