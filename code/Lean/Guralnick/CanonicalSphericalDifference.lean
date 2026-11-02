import Guralnick.CanonicalAuxiliary
import Guralnick.CanonicalFullCorrection

/-! # The actual Laurent difference of consecutive spherical counts -/
noncomputable section
namespace Guralnick.CanonicalSphericalDifference
open Polynomial Positivity CanonicalAuxiliary

/-- The normalized monomial shift is proved directly on Laurent coefficients. -/
theorem normalize_shift (D : ℤ) (k : ℕ) (P : ℤ[X]) :
    normalize D (X^k*P) = normalize (D-2*k) P := by
  have hx : normalize (2*(k : ℤ)) (X^k : ℤ[X]) = (1 : LP) := by
    rw [← monomial_one_right_eq_X_pow,Gaussian.normalize_monomial]
    simp only [sub_self]
    rfl
  have h := Gaussian.normalize_mul (2*(k : ℤ)) (D-2*k) (X^k) P
  rw [hx,one_mul] at h
  convert h using 1 <;> ring

/-- Canonical subtraction produces the manuscript's difference polynomial,
with the power of q determined by the actual change of normalization. -/
theorem consecutive (l h : ℕ) (hh : h+1≤l) :
    sphericalCoefficient (2*l+1) (h+1) - sphericalCoefficient (2*l+1) h =
      CanonicalFullCorrection.transition l (h+1) := by
  have hdegNext : 2*(((h+1)*((2*l+1)-(h+1)) : ℕ) : ℤ) =
      Gaussian.sphericalDegree l (h+1) := by
    simp only [Nat.cast_mul,Nat.cast_sub (show h+1≤2*l+1 by omega),Nat.cast_add,
      Nat.cast_one,Gaussian.sphericalDegree]
    push_cast
    ring
  have hdegPrev : Gaussian.sphericalDegree l (h+1) -
      2*((2*l+1-2*(h+1)+1 : ℕ) : ℤ) = 2*((h*((2*l+1)-h) : ℕ) : ℤ) := by
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_sub (show 2*(h+1)≤2*l+1 by omega),
      Nat.cast_sub (show h≤2*l+1 by omega),Nat.cast_mul,Gaussian.sphericalDegree]
    push_cast
    ring
  unfold CanonicalFullCorrection.transition
  rw [Gaussian.difference,Gaussian.normalize_sub,normalize_shift,hdegPrev]
  unfold sphericalCoefficient
  rw [hdegNext]

end Guralnick.CanonicalSphericalDifference
