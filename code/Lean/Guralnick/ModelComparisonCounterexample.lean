import Guralnick.PolynomialWebLiterature
import Guralnick.PolynomialLatticeBasis
import Guralnick.CoordinateLiteratureTransfer

/-!
# The counterexample through the proved model comparisons

The geometric literature inputs use actual polynomial Laurent lattices.
The cohomological literature inputs use the actual coordinate-ring regular
tensor complex. Both passages to the manuscript's working models are
proved constructions. The general cited theorems themselves remain explicit
arguments; this is not an unconditional disproof in Lean.
-/

noncomputable section
namespace Guralnick.ModelComparisonCounterexample
open scoped BigOperators

/-- The original fixed-source KL row theorem with polynomial-model inputs. -/
theorem row_sum {m : ℕ} (hm : 2 ≤ m) (T : Hecke.Theory (2*m+1))
    (W : PolynomialWebLiterature T) :
    (∑ j : Fin m, Hecke.familyMu hm (show 1 ≤ j.val+1 by omega)
      (show j.val+1 ≤ m by omega) T.kl) = (Nat.choose (m+1) 2 : ℤ) :=
  WebProof.row_sum hm T W.toWebLiterature

/-- The same named highest-weight family, with both characteristic bounds
and the original fixed-source row conclusion retained literally. -/
theorem named_row_and_lower_bound (T : Hecke.TheoryFamily)
    (W : ∀ m hm, PolynomialWebLiterature (T m hm))
    (I : CoordinateLiteratureTransfer.Inputs T)
    (m : ℕ) (hm : 2 ≤ m) (p : ℕ) [Fact p.Prime] (hp : 2*m+1 < p)
    (hp₀ : LiteratureTransfer.threshold I.toFunctionInputs m hm ≤ p)
    (hBNP : 5*(2*m) ≤ p) :
    let A (j : Fin m) := LiteratureTransfer.familyModule I.toFunctionInputs hm
      (show 1 ≤ j.val+1 by omega) (show j.val+1 ≤ m by omega) hp
    (∀ j, Cohomology.AbsolutelyAdmissible (A j)) ∧
    (∀ j, FiniteDimensional (Cohomology.PrimeClosure p) (Cohomology.H1 (A j))) ∧
    2*(∑ j : Fin m, Cohomology.h1Dimension (A j)) = m*(m+1) ∧
    ∃ j : Fin m, m/2+1 ≤ Cohomology.h1Dimension (A j) :=
  WebProof.named_row_and_lower_bound T (fun m hm => (W m hm).toWebLiterature)
    I.toFunctionInputs m hm p hp hp₀ hBNP

/-- The exact original counterexample statement, after both proved model
conversions and with only the documented general literature bundles. -/
theorem not_absoluteBoundedness (T : Hecke.TheoryFamily)
    (W : ∀ m hm, PolynomialWebLiterature (T m hm))
    (I : CoordinateLiteratureTransfer.Inputs T) :
    ¬Cohomology.AbsoluteBoundedness :=
  CoordinateLiteratureTransfer.not_absoluteBoundedness T
    (fun m hm => (W m hm).toWebLiterature) I

end Guralnick.ModelComparisonCounterexample
