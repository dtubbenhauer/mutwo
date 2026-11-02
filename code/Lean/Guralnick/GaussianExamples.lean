import Guralnick.GaussianNormalization

/-! Small exact checks of the correction polynomials, separate from KL
polynomial certificates. `Q_2` is the aggregate corrected polynomial, not
the individual calibration polynomial `P_(w0,C_(2;2))`. -/

noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.Gaussian

theorem Q_two : Q 2 =
    monomial 0 1 + monomial 1 4 + monomial 2 7 + monomial 3 7 + monomial 4 3 := by
  norm_num [Q, Y, M, H, qInteger, difference, qBinomial, Finset.sum_range_succ,
    ← C_mul_X_pow_eq_monomial]
  ring

theorem normalized_Q_two : normalize 9 (Q 2) =
    (Finsupp.single 1 3 + Finsupp.single 3 7 + Finsupp.single 5 7 +
      Finsupp.single 7 4 + Finsupp.single 9 1 : LaurentPolynomial ℤ) := by
  classical
  rw [Q_two]
  simp only [normalize, Polynomial.toFinsupp_add, Polynomial.toFinsupp_monomial]
  repeat rw [Finsupp.mapDomain_add]
  repeat rw [Finsupp.mapDomain_single]
  norm_num
  abel

theorem Q_three_critical : (Q 3).coeff 10 = 6 := by
  have h := (gaussian_cancellation (m := 3) (by omega)).2
  norm_num [criticalDegree] at h
  exact h

end Guralnick.Gaussian
