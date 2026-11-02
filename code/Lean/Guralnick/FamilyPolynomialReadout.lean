import Guralnick.KLFamily
import Guralnick.FidelityKL

/-!
# Recovering a family KL polynomial from its actual source coordinate

The input equality concerns the standard coordinate of an actual canonical
Hecke element. Injectivity of `P ↦ v^D P(v⁻²)` then identifies the ordinary
KL polynomial at the prescribed lower endpoint `w₀`.
-/

noncomputable section
namespace Guralnick.FamilyPolynomialReadout
open Hecke

theorem of_source_coordinate {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    {c : WindowCoxeter (2*m+1)} (K : KLRealization c) (P : Polynomial ℤ)
    (h : K.standard.repr (K.canonical (Family.upper hm hj hjm))
      (AffinePermutation.longest (2*m+1)) = normalize (gapFormula m j) P) :
    K.polynomial (AffinePermutation.longest (2*m+1)) (Family.upper hm hj hjm) = P := by
  apply FidelityKL.normalize_injective (gapFormula m j)
  rw [K.polynomial_normalization, family_length_gap hm hj hjm c] at h
  exact h

end Guralnick.FamilyPolynomialReadout
