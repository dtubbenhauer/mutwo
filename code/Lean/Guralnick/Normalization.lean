import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic

/-!
# The KL parameter conversion, without an assumed KL interpretation

For any genuine polynomial `P`, `normalize D P` is `v^D P(v⁻²)`.
The theorem about its coefficient of `v` is unconditional. Applying it
to a KL polynomial requires supplying that polynomial and proving the
Schur/spherical dictionary separately; no KL values are defined here.
-/
namespace Guralnick
open Polynomial
noncomputable section

noncomputable def normalize (D : ℤ) (P : Polynomial ℤ) : LaurentPolynomial ℤ :=
  Finsupp.mapDomain (fun k : ℕ => D - 2*(k : ℤ)) P.toFinsupp

theorem normalization_exponent_injective (D : ℤ) :
    Function.Injective (fun k : ℕ => D - 2*(k : ℤ)) := by
  intro a b h
  change D - 2*(a : ℤ) = D - 2*(b : ℤ) at h
  exact Int.ofNat.inj (by omega : (a : ℤ) = (b : ℤ))

/-- The exact coefficient conversion. No positivity or degree assumptions on `P` are needed. -/
theorem normalize_critical (P : Polynomial ℤ) (d : ℕ) :
    normalize (2*(d : ℤ)+1) P 1 = P.coeff d := by
  have h := Finsupp.mapDomain_apply (normalization_exponent_injective (2*(d : ℤ)+1))
    P.toFinsupp d
  have he : 2*(d : ℤ)+1-2*(d : ℤ) = 1 := by ring
  rw [he] at h
  exact h

/-- The displayed length-gap formula. It is not defined to be Coxeter length. -/
def gapFormula (m j : ℕ) : ℤ :=
  2*(j : ℤ)*(2*(m : ℤ)+1-j)-2*((m : ℤ)-j)-3

def criticalIndex (m j : ℕ) : ℕ :=
  ((j : ℤ)*(2*(m : ℤ)+1-j)-((m : ℤ)-j)-2).toNat

theorem gapFormula_odd {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    gapFormula m j = 2*(criticalIndex m j : ℤ)+1 := by
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hjm' : (j : ℤ) ≤ m := by exact_mod_cast hjm
  have hprod : 0 ≤ ((j : ℤ)-1)*((m : ℤ)+1) :=
    mul_nonneg (by omega) (by omega)
  have hprod' : 0 ≤ (j : ℤ)*((m : ℤ)-j) :=
    mul_nonneg (by omega) (by omega)
  have hn : 0 ≤ (j : ℤ)*(2*(m : ℤ)+1-j)-((m : ℤ)-j)-2 := by nlinarith
  simp only [gapFormula, criticalIndex, Int.toNat_of_nonneg hn]
  ring

theorem normalize_family_critical (P : Polynomial ℤ) {m j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ m) :
    normalize (gapFormula m j) P 1 = P.coeff (criticalIndex m j) := by
  rw [gapFormula_odd hj hjm]
  exact normalize_critical P _

/-- The manuscript's calibration polynomial, named as supplied data, not defined as a KL polynomial. -/
def suppliedSeedPolynomial : Polynomial ℤ :=
  monomial 0 1 + monomial 1 4 + monomial 2 5 + monomial 3 4 + monomial 4 2

theorem suppliedSeedPolynomial_display : suppliedSeedPolynomial =
    1 + 4*X + 5*X^2 + 4*X^3 + 2*X^4 := by
  simp only [suppliedSeedPolynomial, ← Polynomial.C_mul_X_pow_eq_monomial]
  norm_num

theorem suppliedSeed_critical : normalize 9 suppliedSeedPolynomial 1 = 2 := by
  have h := normalize_critical suppliedSeedPolynomial 4
  simpa [suppliedSeedPolynomial, Polynomial.coeff_add, Polynomial.coeff_monomial,
    Polynomial.coeff_one] using h

/-- The full displayed reversal is checked coefficientwise, as a Laurent polynomial. -/
theorem suppliedSeed_full : normalize 9 suppliedSeedPolynomial =
    (Finsupp.single 1 2 + Finsupp.single 3 4 + Finsupp.single 5 5 +
      Finsupp.single 7 4 + Finsupp.single 9 1 : LaurentPolynomial ℤ) := by
  classical
  simp only [normalize, suppliedSeedPolynomial, Polynomial.toFinsupp_add,
    Polynomial.toFinsupp_monomial]
  repeat rw [Finsupp.mapDomain_add]
  repeat rw [Finsupp.mapDomain_single]
  norm_num
  abel

end
end Guralnick
