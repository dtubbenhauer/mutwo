import Guralnick.RationalCoordinateRepresentations
import Guralnick.SLCoordinateReduced
import Guralnick.SLCoordinateHopf
import Guralnick.WebProof

/-!
# Literature transfer through the proved coordinate-cochain comparison

The external H¹ statements here concern the actual regular tensor complex.
The old polynomial-function interfaces are derived by `h1Equiv`; no
model-comparison field is assumed. Jantzen's derived-cohomology theorem is
still part of the cited interpretation of Andersen/AJS and BNP.
-/

noncomputable section
namespace Guralnick.CoordinateLiteratureTransfer
open HighestWeight LiteratureTransfer RationalCoordinate

/-- Andersen/AJS with the same labels and hypotheses, on coordinate cohomology. -/
def AndersenAJS (T : Hecke.TheoryFamily) : Prop :=
  ∀ (m : ℕ) (hm : 2 ≤ m), ∃ p₀ : ℕ,
    ∀ (p : ℕ) (hp : p.Prime), p₀ ≤ p → 2 * m + 1 < p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (wt : Weights.RootLattice (2 * m + 1))
        (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)
        (b : AffinePermutation (2 * m + 1)),
        finiteLeftMinimal (T m hm).coxeter b →
        DominantRestricted (p : ℤ) wt.val →
        wt.val = b.dotZero (p : ℤ) (Weights.rho m) →
        letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
        (Module.finrank (Cohomology.PrimeClosure p) (CoordinateH1 A.polynomial) : ℤ) =
          ((T m hm).kl.standard.repr ((T m hm).kl.canonical
            (AffinePermutation.longest (2 * m + 1) * b))
            (AffinePermutation.longest (2 * m + 1))) 1

/-- BNP on the coordinate complex, retaining its restricted prime-field hypotheses. -/
def BNP : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime), 5 * (2 * m) ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (wt : Weights.RootLattice (2 * m + 1))
      (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)
      (b : AffinePermutation (2 * m + 1)),
      DominantRestricted (p : ℤ) wt.val →
      wt.val = b.dotZero (p : ℤ) (Weights.rho m) →
      letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
      Nonempty (CoordinateH1 A.polynomial ≃ₗ[Cohomology.PrimeClosure p]
        Cohomology.H1 (restrictPrime (2 * m + 1) p A.rep))

/-- Only the previously documented general cited theorems occur as fields. -/
structure Inputs (T : Hecke.TheoryFamily) : Prop where
  existence : LiteratureTransfer.HighestWeightExistence
  andersen : AndersenAJS T
  bnp : BNP
  steinberg : LiteratureTransfer.Steinberg
  simple : LiteratureTransfer.PSLSimplicity

theorem andersen_to_function {T : Hecke.TheoryFamily} (h : AndersenAJS T) :
    LiteratureTransfer.AndersenAJS T := by
  intro m hm
  obtain ⟨p₀, hp₀⟩ := h m hm
  refine ⟨p₀, ?_⟩
  intro p hp hbound hlarge
  letI : Fact p.Prime := ⟨hp⟩
  intro wt A b hmin hdom hlabel
  letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
  have hdim := hp₀ p hp hbound hlarge wt A b hmin hdom hlabel
  rw [← h1_finrank A.polynomial]
  exact hdim

theorem bnp_to_function (h : BNP) : LiteratureTransfer.BNP := by
  intro m hm p hp hbound
  letI : Fact p.Prime := ⟨hp⟩
  intro wt A b hdom hlabel
  letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
  obtain ⟨e⟩ := h m hm p hp hbound wt A b hdom hlabel
  exact ⟨(h1Equiv A.polynomial).symm.trans e⟩

/-- Changing cochain models does not strengthen or weaken the Andersen input. -/
theorem andersen_iff_function {T : Hecke.TheoryFamily} :
    AndersenAJS T ↔ LiteratureTransfer.AndersenAJS T := by
  refine ⟨andersen_to_function, ?_⟩
  intro h m hm
  obtain ⟨p₀, hp₀⟩ := h m hm
  refine ⟨p₀, ?_⟩
  intro p hp hbound hlarge
  letI : Fact p.Prime := ⟨hp⟩
  intro wt A b hmin hdom hlabel
  letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
  have hdim := hp₀ p hp hbound hlarge wt A b hmin hdom hlabel
  rw [h1_finrank A.polynomial]
  exact hdim

/-- The same exact equivalence holds for the BNP statement. -/
theorem bnp_iff_function : BNP ↔ LiteratureTransfer.BNP := by
  refine ⟨bnp_to_function, ?_⟩
  intro h m hm p hp hbound
  letI : Fact p.Prime := ⟨hp⟩
  intro wt A b hdom hlabel
  letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
  obtain ⟨e⟩ := h m hm p hp hbound wt A b hdom hlabel
  exact ⟨(h1Equiv A.polynomial).trans e⟩

/-- The model comparison is a proved construction, not a new literature input. -/
def Inputs.toFunctionInputs {T : Hecke.TheoryFamily} (I : Inputs T) :
    LiteratureTransfer.Inputs T where
  existence := I.existence
  andersen := andersen_to_function I.andersen
  bnp := bnp_to_function I.bnp
  steinberg := I.steinberg
  simple := I.simple

/-- The final counterexample now explicitly passes through the checked
coordinate-to-function cohomology comparison. -/
theorem not_absoluteBoundedness (T : Hecke.TheoryFamily)
    (W : ∀ m hm, WebLiterature (T m hm)) (I : Inputs T) :
    ¬Cohomology.AbsoluteBoundedness :=
  WebProof.not_absoluteBoundedness T W I.toFunctionInputs

end Guralnick.CoordinateLiteratureTransfer
