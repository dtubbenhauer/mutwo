import Guralnick.MainContributionBounds
import Guralnick.Counterexample
import Guralnick.WebGraphProof

/-!
# The manuscript's counterexample, modulo the explicit general literature

No original row sum, auxiliary canonicality, gallery coefficient, or family
cohomology equality is a hypothesis of the theorems in this file. Those
steps are proved in the imported modules. The remaining hypotheses are
exactly the general framework and representation-theoretic inputs listed
in literature-inputs.md; their existence is not proved here.
-/
noncomputable section
open scoped BigOperators
namespace Guralnick.WebProof

/-- The original fixed-source ordinary KL row theorem. -/
theorem row_sum {m : ℕ} (hm : 2≤m) (T : Hecke.Theory (2*m+1)) (W : WebLiterature T) :
    (∑ j : Fin m, Hecke.familyMu hm (show 1≤j.val+1 by omega)
      (show j.val+1≤m by omega) T.kl) = (Nat.choose (m+1) 2 : ℤ) :=
  WebLiterature.row_sum_of_contribution_bounds hm T W
    (WebLiterature.auxiliary_family_bound hm T W)
    (WebLiterature.nonspherical_bound hm T W)
    (WebLiterature.auxiliary_source_bound hm T W)

/-- The critical coefficient of the corrected evaluated graph is the
actual fixed-w0 ordinary KL row. The whole graph-to-raw bridge is proved
in WebGraphProof, including equality of the right Hecke-module maps. -/
theorem graph_critical_eq_row_sum {m : ℕ} (hm : 2≤m)
    (T : Hecke.Theory (2*m+1)) (W : WebLiterature T) :
    T.kl.standard.repr (graphCorrected hm T W) (AffinePermutation.longest (2*m+1)) 1=
      ∑ j : Fin m, Hecke.familyMu hm (show 1≤j.val+1 by omega)
        (show j.val+1≤m by omega) T.kl :=
  (graph_corrected_critical hm T W).trans (row_sum hm T W).symm

/-- Small-rank checks of the proved row theorem, not supplied KL tables. -/
theorem row_two (T : Hecke.Theory 5) (W : WebLiterature T) :
    (∑ j : Fin 2, Hecke.familyMu (by decide : 2≤2) (show 1≤j.val+1 by omega)
      (show j.val+1≤2 by omega) T.kl) = 3 := by
  simpa using row_sum (by decide : 2≤2) T W

theorem row_three (T : Hecke.Theory 7) (W : WebLiterature T) :
    (∑ j : Fin 3, Hecke.familyMu (by decide : 2≤3) (show 1≤j.val+1 by omega)
      (show j.val+1≤3 by omega) T.kl) = 6 := by
  simpa using row_sum (by decide : 2≤3) T W

variable (T : Hecke.TheoryFamily) (W : ∀ m hm, WebLiterature (T m hm))
include W

theorem doubled_row_sum : Cohomology.DoubledRowSum (Hecke.coefficients T) :=
  Counterexample.doubledRowSum_of_kl_rows T (fun m hm => row_sum hm (T m hm) (W m hm))

/-- The named highest-weight modules, their actual finite-group H¹ row,
and an unbounded maximum, with the separate AJS and BNP bounds visible. -/
theorem named_row_and_lower_bound (I : LiteratureTransfer.Inputs T)
    (m : ℕ) (hm : 2≤m) (p : ℕ) [Fact p.Prime] (hp : 2*m+1<p)
    (hp₀ : LiteratureTransfer.threshold I m hm≤p) (hBNP : 5*(2*m)≤p) :
    let A (j : Fin m) := LiteratureTransfer.familyModule I hm
      (show 1≤j.val+1 by omega) (show j.val+1≤m by omega) hp
    (∀ j, Cohomology.AbsolutelyAdmissible (A j)) ∧
    (∀ j, FiniteDimensional (Cohomology.PrimeClosure p) (Cohomology.H1 (A j))) ∧
    2*(∑ j : Fin m, Cohomology.h1Dimension (A j))=m*(m+1) ∧
    ∃ j : Fin m, m/2+1≤Cohomology.h1Dimension (A j) :=
  Counterexample.named_row_and_lower_bound T I (doubled_row_sum T W) m hm p hp hp₀ hBNP

/-- Negation of the precise absolute boundedness conjecture, conditional
only on the explicitly stated general literature inputs. -/
theorem not_absoluteBoundedness (I : LiteratureTransfer.Inputs T) :
    ¬Cohomology.AbsoluteBoundedness :=
  Counterexample.not_absoluteBoundedness T I (doubled_row_sum T W)

end Guralnick.WebProof
