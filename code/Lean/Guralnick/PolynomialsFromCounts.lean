import Guralnick.GaussianNormalization
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Polynomial.Roots

/-!
# Laurent identities from finite-field counting specializations

At cardinality p² the convention is v=1/p, since Q=v⁻². Equality at every
prime specialization determines the integer Laurent polynomial. This
interpolation step is proved, not an assumed convolution theorem.
-/
noncomputable section
namespace Guralnick.PolynomialsFromCounts
open Polynomial LaurentPolynomial
abbrev LP := LaurentPolynomial ℤ

def primeUnit (p : ℕ) (hp : p.Prime) : ℚˣ :=
  (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero))⁻¹

def specialize (p : ℕ) (hp : p.Prime) : LP →+* ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℚ) (primeUnit p hp)

theorem zero_of_prime_specializations (f : LP)
    (h : ∀ (p : ℕ) (hp : p.Prime), specialize p hp f = 0) : f = 0 := by
  obtain ⟨n, P, hP⟩ := LaurentPolynomial.exists_T_pow f
  have hinf : Set.Infinite ((fun p : ℕ => (p : ℚ)⁻¹) '' {p | p.Prime}) :=
    Nat.infinite_setOf_prime.image (by
      intro a _ b _ hab
      exact_mod_cast (inv_injective hab : (a : ℚ) = (b : ℚ)))
  have hz : P.map (Int.castRingHom ℚ) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hinf.mono
    rintro x ⟨p, hp, rfl⟩
    change (P.map (Int.castRingHom ℚ)).eval ((p : ℚ)⁻¹) = 0
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ (Int.castRingHom ℚ) (primeUnit p hp).val P = 0
    rw [← LaurentPolynomial.eval₂_toLaurent]
    rw [hP, map_mul]
    change specialize p hp f * _ = 0
    rw [h p hp, zero_mul]
  have hPzero : P = 0 := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [Polynomial.map_zero] using hz
  have hf : f * T (n : ℤ) = 0 := by rw [← hP, hPzero, map_zero]
  exact (mul_eq_zero.mp hf).resolve_right (isUnit_T (n : ℤ)).ne_zero

theorem eq_of_prime_specializations (f g : LP)
    (h : ∀ (p : ℕ) (hp : p.Prime), specialize p hp f = specialize p hp g) : f = g := by
  apply sub_eq_zero.mp
  apply zero_of_prime_specializations
  intro p hp
  rw [map_sub, h p hp, sub_self]

theorem eval_normalize (u : ℚˣ) (d : ℤ) (P : ℤ[X]) :
    LaurentPolynomial.eval₂ (Int.castRingHom ℚ) u (normalize d P) =
      (u ^ d).val * Polynomial.eval₂ (Int.castRingHom ℚ) (u ^ (-2 : ℤ)).val P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Gaussian.normalize_add, map_add, Polynomial.eval₂_add, hP, hQ, mul_add]
  | monomial n a =>
      rw [Gaussian.normalize_monomial, LaurentPolynomial.single_eq_C_mul_T,
        LaurentPolynomial.eval₂_C_mul_T, Polynomial.eval₂_monomial]
      rw [show d - 2*(n : ℤ) = d + (-2)*(n : ℤ) by ring,
        zpow_add, zpow_mul, zpow_natCast]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring

theorem primeUnit_parameter (p : ℕ) (hp : p.Prime) :
    ((primeUnit p hp) ^ (-2 : ℤ)).val = (p : ℚ)^2 := by
  simp only [primeUnit, zpow_neg, inv_inv, Units.val_pow_eq_pow_val,
    Units.val_zpow_eq_zpow_val, Units.val_mk0]
  norm_num
  exact zpow_natCast (p : ℚ) 2

theorem specialize_normalize (p : ℕ) (hp : p.Prime) (d : ℤ) (P : ℤ[X]) :
    specialize p hp (normalize d P) =
      ((primeUnit p hp)^d).val * Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2) P := by
  rw [specialize, eval_normalize, primeUnit_parameter]

/-- An actual finite-field count determines the normalized coefficient. -/
theorem normalized_of_count_specializations (f : LP) (d : ℤ) (P : ℤ[X])
    (h : ∀ (p : ℕ) (hp : p.Prime), specialize p hp f =
      ((primeUnit p hp)^d).val * Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2) P) :
    f = normalize d P := by
  apply eq_of_prime_specializations
  intro p hp
  rw [specialize_normalize]
  exact h p hp

end Guralnick.PolynomialsFromCounts
