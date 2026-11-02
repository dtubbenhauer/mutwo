import Guralnick.FullFlagHeckeConvolution
import Guralnick.PolynomialConvolutionNormalization
import Guralnick.PolynomialFlagExtension

/-!
# Cardinality of actual full lifts

The full-flag convolution theorem evaluates the square of the actual
finite-parabolic symmetrizer. Its proved absorption identity and proved
scalar normalization then determine the lift cardinality. Existence of a
full lift for every partial flag is constructed independently, so no
parabolic fiber count or refinement existence is an additional input.
-/
noncomputable section
namespace Guralnick.PolynomialFullLiftCardinality
open Hecke ParabolicWeb PolynomialFullGallery PolynomialsFromCounts
open PolynomialConvolutionNormalization FullFlagHeckeConvolution

variable {n : ℕ} [NeZero n] {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)
variable (p : ℕ) [Fact p.Prime] (hp : p.Prime) (C : Input K p hp)
include L C

/-- A fiber over an existing full flag has the actual finite-parabolic
Poincare cardinality. This is cancellation in the symmetrizer square. -/
theorem lift_card_forget (I : Index n) (E : FullFlag (GaloisField p 2) n) :
    (Nat.card (Lift (forget I E)) : ℚ) = PoincareValue D p I := by
  have h := symmetrizer_square_count K p hp D L C I E
  rw [scalar_specialize] at h
  symm
  apply mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero
    ((primeUnit p hp) ^ (c.system.length (D I).longest.val : ℤ))))
  calc
    (((primeUnit p hp) ^ (c.system.length (D I).longest.val : ℤ)).val)^2 *
        PoincareValue D p I =
      (((primeUnit p hp) ^ (c.system.length (D I).longest.val : ℤ)).val *
        PoincareValue D p I) *
        ((primeUnit p hp) ^ (c.system.length (D I).longest.val : ℤ)).val := by ring
    _ = _ := h

/-- Every actual polynomial partial flag has this cardinality. Full
refinements are constructed by finite-dimensional flag extension. -/
theorem lift_card_eq {I : Index n}
    (F : PolynomialFlags.Flag (GaloisField p 2) n (LatticeFlags.retained I)) :
    (Nat.card (Lift F) : ℚ) = PoincareValue D p I := by
  obtain ⟨E,hE⟩ := PolynomialFlagExtension.lift_nonempty F
  rw [←hE]
  exact lift_card_forget K D L p hp C I E

/-- At the boundary retaining every node the fiber and Poincare value are
both one, with no quotient or nontrivial flag choice. -/
theorem full_poincareValue_eq_one (E : FullFlag (GaloisField p 2) n) :
    PoincareValue D p (fullIndex n) = 1 := by
  rw [←lift_card_eq K D L p hp C E,PolynomialFlagExtension.full_lift_card]
  norm_num

#print axioms lift_card_forget
#print axioms lift_card_eq
#print axioms full_poincareValue_eq_one
end Guralnick.PolynomialFullLiftCardinality
