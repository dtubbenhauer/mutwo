import Guralnick.GaussianNormalization
import Guralnick.CanonicalCorrection

/-!
# Descending correction with the manuscript's actual Gaussian coefficients

The proposed residual is no longer a hypothesis: Gaussian cancellation
proves it. The remaining application input is the actual full-spherical
coordinate expansion, after the other canonical families have been shown
to have positive support at those coordinates.
-/

noncomputable section

namespace Guralnick.CanonicalFullCorrection

open scoped BigOperators
open Positivity CanonicalCorrection

def rawCoordinate (l : ℕ) : LP :=
  normalize (Gaussian.normalizationDegree l) (Gaussian.Y l)

def transition (l h : ℕ) : LP :=
  normalize (Gaussian.sphericalDegree l h) (Gaussian.difference (2*l+1) h)

def residual (a : ℕ → LP) (l : ℕ) : LP :=
  rawCoordinate l - ∑ h ∈ Finset.range (l-1), a (l-h) * transition l h

@[simp] theorem transition_zero (l : ℕ) : transition l 0 = 1 := by
  unfold transition
  simp only [Gaussian.sphericalDegree, Nat.cast_zero, mul_zero, zero_mul,
    Gaussian.difference_zero]
  have h : normalize 0 (1 : Polynomial ℤ) = (LaurentPolynomial.C 1 : LP) := by
    change Finsupp.mapDomain (fun k : ℕ => (0 : ℤ)-2*k) (Finsupp.single 0 1) =
      Finsupp.single 0 1
    rw [Finsupp.mapDomain_single]
    norm_num
  simpa only [map_one] using h

theorem proposed_residual (l : ℕ) :
    residual correction l = normalize (Gaussian.normalizationDegree l) (Gaussian.Q l) :=
  Gaussian.full_spherical_residual l

theorem proposed_residual_positive {l : ℕ} (hl : 2 ≤ l) :
    LowerBound (residual correction l) 1 := Gaussian.full_spherical_residual_lowerBound hl

/-- The manuscript's descending recovery, with explicit Gaussian
coordinates and correction. The proposed formula is proved; only the
actual coordinate expansion (encoded by the positivity of its residual)
remains to be instantiated from the web's canonical expansion. -/
theorem correction_unique (a : ℕ → LP)
    (hbar : ∀ l, 2 ≤ l → BarSymmetric (a l))
    (hactual : ∀ l, 2 ≤ l → LowerBound (residual a l) 1) :
    ∀ l, 2 ≤ l → a l = correction l := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      intro hl
      classical
      have hzero : 0 ∈ Finset.range (l-1) := Finset.mem_range.mpr (by omega)
      have htail :
          (∑ h ∈ (Finset.range (l-1)).erase 0, a (l-h) * transition l h) =
          ∑ h ∈ (Finset.range (l-1)).erase 0, correction (l-h) * transition l h := by
        apply Finset.sum_congr rfl
        intro h hh
        obtain ⟨hh0, hhr⟩ := Finset.mem_erase.mp hh
        have hhl := Finset.mem_range.mp hhr
        rw [ih (l-h) (by omega) (by omega)]
      have hsplit (f : ℕ → LP) :
          (∑ h ∈ Finset.range (l-1), f (l-h) * transition l h) =
          f l + ∑ h ∈ (Finset.range (l-1)).erase 0, f (l-h) * transition l h := by
        rw [← Finset.add_sum_erase _ _ hzero]
        simp only [Nat.sub_zero, transition_zero, mul_one]
      have heq : residual correction l - residual a l = a l - correction l := by
        unfold residual
        rw [hsplit, hsplit, htail]
        abel
      apply eq_of_positive_difference (hbar l hl) (correction_bar l)
      have h := lowerBound_sub (proposed_residual_positive hl) (hactual l hl)
      rwa [heq] at h

/-- The finite-rank form needed for a single six-map web: no hypotheses
about larger ranks or other members of the family are needed. -/
theorem correction_unique_up_to (m : ℕ) (a : ℕ → LP)
    (hbar : ∀ l, 2 ≤ l → l ≤ m → BarSymmetric (a l))
    (hactual : ∀ l, 2 ≤ l → l ≤ m → LowerBound (residual a l) 1) :
    ∀ l, 2 ≤ l → l ≤ m → a l = correction l := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      intro hl hlm
      classical
      have hzero : 0 ∈ Finset.range (l-1) := Finset.mem_range.mpr (by omega)
      have htail :
          (∑ h ∈ (Finset.range (l-1)).erase 0, a (l-h) * transition l h) =
          ∑ h ∈ (Finset.range (l-1)).erase 0, correction (l-h) * transition l h := by
        apply Finset.sum_congr rfl
        intro h hh
        obtain ⟨hh0, hhr⟩ := Finset.mem_erase.mp hh
        have hhl := Finset.mem_range.mp hhr
        rw [ih (l-h) (by omega) (by omega) (by omega)]
      have hsplit (f : ℕ → LP) :
          (∑ h ∈ Finset.range (l-1), f (l-h) * transition l h) =
          f l + ∑ h ∈ (Finset.range (l-1)).erase 0, f (l-h) * transition l h := by
        rw [← Finset.add_sum_erase _ _ hzero]
        simp only [Nat.sub_zero, transition_zero, mul_one]
      have heq : residual correction l - residual a l = a l - correction l := by
        unfold residual
        rw [hsplit, hsplit, htail]
        abel
      apply eq_of_positive_difference (hbar l hl hlm) (correction_bar l)
      have h := lowerBound_sub (proposed_residual_positive hl) (hactual l hl hlm)
      rwa [heq] at h

/-- The corrected full-spherical coordinate has exactly the paper's
critical coefficient, independently of any separate numerical recurrence. -/
theorem corrected_critical {l : ℕ} (hl : 2 ≤ l) :
    residual correction l 1 = (Nat.choose (l+1) 2 : ℤ) := by
  rw [proposed_residual]
  exact Gaussian.normalized_Q_critical hl

end Guralnick.CanonicalFullCorrection
