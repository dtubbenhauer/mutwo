import Guralnick.LiteratureTransfer

/-!
# The exact named-module application, conditional on the remaining web theorem

The representation-theoretic inputs here are the precise general literature
statements of `LiteratureTransfer.Inputs`. The numerical input is explicitly
the ORIGINAL fixed-source KL row-sum theorem. It is not a literature input.
The later `WebProof` module discharges that original obligation and supplies
the final conclusion with only general literature hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace Guralnick.Counterexample
open Cohomology LiteratureTransfer

variable (T : Hecke.TheoryFamily) (I : Inputs T)

/-- Conversion from the actual integer-valued fixed-source KL row to the
natural-valued row used in the cohomological application. Nonnegativity,
and hence the validity of `toNat`, comes from ordinary KL positivity. -/
theorem doubledRowSum_of_kl_rows
    (hrow : ∀ (m : ℕ) (hm : 2 ≤ m),
      (∑ j : Fin m, Hecke.familyMu hm (show 1 ≤ j.val+1 by omega)
        (show j.val+1 ≤ m by omega) (T m hm).kl) = (Nat.choose (m+1) 2 : ℤ)) :
    DoubledRowSum (Hecke.coefficients T) := by
  intro m hm
  have hs : (∑ j : Fin m, Hecke.coefficients T m (j.val+1)) = Nat.choose (m+1) 2 := by
    have hc (j : Fin m) := Hecke.coefficients_cast T hm
      (show 1 ≤ j.val+1 by omega) (show j.val+1 ≤ m by omega)
    have hr : (∑ j : Fin m, (Hecke.coefficients T m (j.val+1) : ℤ)) =
        (Nat.choose (m+1) 2 : ℤ) := by
      simpa only [hc] using hrow m hm
    exact_mod_cast hr
  rw [hs]
  have hc := Nat.choose_succ_right_eq (m+1) 1
  simpa only [Nat.choose_one_right, Nat.add_sub_cancel, Nat.mul_comm] using hc

/-- The named modules of the paper, with the exact row sum and maximum
lower bound, at every sufficiently large prime. Absolute irreducibility is
the actual scalar-extension predicate, not an unproved annotation. -/
theorem named_row_and_lower_bound
    (hrow : DoubledRowSum (Hecke.coefficients T)) (m : ℕ) (hm : 2 ≤ m)
    (p : ℕ) [Fact p.Prime] (hp : 2*m+1 < p)
    (hp₀ : threshold I m hm ≤ p) (hBNP : 5*(2*m) ≤ p) :
    let A (j : Fin m) := familyModule I hm (show 1 ≤ j.val+1 by omega)
      (show j.val+1 ≤ m by omega) hp
    (∀ j, AbsolutelyAdmissible (A j)) ∧
    (∀ j, FiniteDimensional (PrimeClosure p) (H1 (A j))) ∧
    2 * (∑ j : Fin m, h1Dimension (A j)) = m*(m+1) ∧
    ∃ j : Fin m, m/2+1 ≤ h1Dimension (A j) := by
  dsimp only
  let A (j : Fin m) := familyModule I hm (show 1 ≤ j.val+1 by omega)
    (show j.val+1 ≤ m by omega) hp
  have hdim (j : Fin m) : h1Dimension (A j) = Hecke.coefficients T m (j.val+1) :=
    familyModule_h1_dimension I hm (by omega) (by omega) hp hp₀ hBNP
  have hsum : 2 * (∑ j : Fin m, h1Dimension (A j)) = m*(m+1) := by
    simpa only [hdim] using hrow m hm
  refine ⟨?_, ?_, hsum, ?_⟩
  · intro j
    exact familyModule_absolutelyAdmissible I hm (by omega) (by omega) hp hBNP
  · intro j
    have hA := familyModule_admissible I hm (show 1 ≤ j.val+1 by omega)
      (show j.val+1 ≤ m by omega) hp hBNP
    letI : FiniteDimensional (PrimeClosure p) (A j) := hA.1
    exact finiteDimensional_H1 (A j)
  · obtain ⟨j, hj⟩ := exists_entry_gt_of_row (m := m) (C := m/2)
      (fun j => h1Dimension (A j)) (by omega) (by omega) hsum
    exact ⟨j, Nat.succ_le_iff.mpr hj⟩

/-- The precise all-field boundedness conjecture is false IF the original
fixed-source row theorem is supplied, modulo the general literature inputs.
The hypothesis is deliberately visible; this is not an unconditional disproof. -/
theorem not_absoluteBoundedness (I : Inputs T)
    (hrow : DoubledRowSum (Hecke.coefficients T)) : ¬AbsoluteBoundedness :=
  not_absoluteBoundedness_of_row_and_transfer (Hecke.coefficients T) hrow
    (primeFieldTransfer I)

end Guralnick.Counterexample
