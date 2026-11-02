import Guralnick.GaussianSeries

/-!
# The original critical cancellation in low degrees

This file proves the manuscript's finite correction calculation. The
polynomials and series are independently defined; no recurrence for the
answer and no row-sum identity is assumed.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.Gaussian

/-- The polynomial expression obtained by reversing the summands about
`topDegree m`. Its identification with the reversal of `Q` is separate. -/
def reversedCorrection (m : ℕ) : ℤ[X] :=
  Y m - ∑ r ∈ Finset.range (m-1), X^r * H (m-r) * delta (2*m+1) r

/-- Weighted finite differences telescope, including the final boundary term. -/
theorem weighted_delta_telescoping (n s : ℕ) :
    (∑ r ∈ Finset.range (s+1), PowerSeries.X^r * (delta n r : PowerSeries ℤ)) =
      (1-PowerSeries.X) *
        (∑ r ∈ Finset.range (s+1), PowerSeries.X^r * (qBinomial n r : PowerSeries ℤ)) +
      PowerSeries.X^(s+1)*(qBinomial n s : PowerSeries ℤ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    conv_lhs => rw [Finset.sum_range_succ]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [ih]
    simp only [delta, Polynomial.coe_sub, pow_succ]
    ring

/-- The only boundary term in weighted telescoping is above the truncation. -/
theorem weighted_delta_low {m : ℕ} (hm : 1 ≤ m) :
    LowEq m (∑ r ∈ Finset.range m, PowerSeries.X^r *
      (delta (2*m+1) r : PowerSeries ℤ))
      ((1-PowerSeries.X)*inversePochhammer (m-1)) := by
  have he : (∑ r ∈ Finset.range m, PowerSeries.X^r *
      (delta (2*m+1) r : PowerSeries ℤ)) =
      (1-PowerSeries.X) *
        (∑ r ∈ Finset.range m, PowerSeries.X^r * (qBinomial (2*m+1) r : PowerSeries ℤ)) +
      PowerSeries.X^m*(qBinomial (2*m+1) (m-1) : PowerSeries ℤ) := by
    simpa only [Nat.sub_add_cancel hm] using weighted_delta_telescoping (2*m+1) (m-1)
  rw [he]
  simpa using ((weighted_qBinomial_low hm).mul_left (1-PowerSeries.X)).add
    (LowEq.shift_zero m (qBinomial (2*m+1) (m-1) : PowerSeries ℤ))

/-- At the last retained degree, multiplication only sees a constant term. -/
theorem last_monomial_mul_low {m : ℕ} (hm : 1 ≤ m) (a : ℤ) (f : PowerSeries ℤ) :
    LowEq m ((PowerSeries.C ℤ a * PowerSeries.X^(m-1))*f)
      (PowerSeries.C ℤ (a * PowerSeries.coeff ℤ 0 f) * PowerSeries.X^(m-1)) := by
  intro k hk
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases h : m-1 ≤ k
  · have he : k = m-1 := by omega
    subst k
    simp
  · simp [h, show k ≠ m-1 by omega]

/-- The local truncation defect vanishes for every `r>0` because the
constant term of the corresponding Gaussian difference is zero. -/
theorem corrected_summand_low {m r : ℕ} (hr : r < m) :
    LowEq m (PowerSeries.X^r * (H (m-r) : PowerSeries ℤ) *
      (delta (2*m+1) r : PowerSeries ℤ))
      (inversePower 4 * (PowerSeries.X^r * (delta (2*m+1) r : PowerSeries ℤ)) -
        if r = 0 then PowerSeries.C ℤ (Nat.choose (m+1) 2 : ℤ) * PowerSeries.X^(m-1)
        else 0) := by
  have hfirst := (shifted_H_low hr).mul_right (delta (2*m+1) r : PowerSeries ℤ)
  have hlast := last_monomial_mul_low (m := m) (by omega)
    (Nat.choose (m-r+1) 2 : ℤ) (delta (2*m+1) r : PowerSeries ℤ)
  rw [Polynomial.coeff_coe, delta_const (by omega : r ≤ 2*m+1)] at hlast
  by_cases hr0 : r = 0
  · subst r
    simp only [Nat.sub_zero, if_pos rfl, mul_one] at hlast
    have hsecond := (LowEq.refl m
      (inversePower 4 * (PowerSeries.X^0*(delta (2*m+1) 0 : PowerSeries ℤ)))).sub hlast
    apply hfirst.trans
    convert hsecond using 1 <;> simp <;> ring
  · simp only [if_neg hr0, mul_zero, map_zero, zero_mul] at hlast
    have hsecond := (LowEq.refl m
      (inversePower 4 * (PowerSeries.X^r*(delta (2*m+1) r : PowerSeries ℤ)))).sub hlast
    apply hfirst.trans
    convert hsecond using 1 <;> simp [hr0] <;> ring

/-- Sum of the actual correction terms, extended by the zero `H_1` term. -/
theorem correction_sum_low {m : ℕ} (hm : 1 ≤ m) :
    LowEq m
      (∑ r ∈ Finset.range m, PowerSeries.X^r * (H (m-r) : PowerSeries ℤ) *
        (delta (2*m+1) r : PowerSeries ℤ))
      (inversePower 4 *
        (∑ r ∈ Finset.range m, PowerSeries.X^r * (delta (2*m+1) r : PowerSeries ℤ)) -
        PowerSeries.C ℤ (Nat.choose (m+1) 2 : ℤ) * PowerSeries.X^(m-1)) := by
  have h := LowEq.sum (Finset.range m)
    (fun r hr => corrected_summand_low (Finset.mem_range.mp hr))
  have hsum : (∑ r ∈ Finset.range m,
      if r = 0 then PowerSeries.C ℤ (Nat.choose (m+1) 2 : ℤ) * PowerSeries.X^(m-1)
      else (0 : PowerSeries ℤ)) =
        PowerSeries.C ℤ (Nat.choose (m+1) 2 : ℤ) * PowerSeries.X^(m-1) := by
    simp [show 0 < m by omega]
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum] using h

/-- `H_1=0` justifies including the endpoint in the finite telescope. -/
theorem correction_sum_extend {m : ℕ} (hm : 1 ≤ m) :
    (∑ r ∈ Finset.range (m-1), PowerSeries.X^r * (H (m-r) : PowerSeries ℤ) *
      (delta (2*m+1) r : PowerSeries ℤ)) =
    (∑ r ∈ Finset.range m, PowerSeries.X^r * (H (m-r) : PowerSeries ℤ) *
      (delta (2*m+1) r : PowerSeries ℤ)) := by
  have he : m-1+1 = m := by omega
  conv_rhs => rw [← he, Finset.sum_range_succ]
  have hidx : m-(m-1) = 1 := by omega
  simp only [he, hidx, H_one, Polynomial.coe_zero, mul_zero, zero_mul, add_zero]

/-- Multiplication by `1-q` lowers the inverse fourth power to the third. -/
theorem inversePower_four_mul_one_sub : inversePower 4 * (1-PowerSeries.X) =
    inversePower 3 := by
  simpa only [inversePower, pow_one, mul_comm] using
    PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val (S := ℤ) 3 1

/-- The original critical cancellation, uniformly in `m`, for the explicit
reversed polynomial. All its q-series and binomial ingredients are proved. -/
theorem reversedCorrection_low {m : ℕ} (hm : 1 ≤ m) :
    LowEq m (reversedCorrection m : PowerSeries ℤ)
      (PowerSeries.C ℤ (Nat.choose (m+1) 2 : ℤ) * PowerSeries.X^(m-1)) := by
  have hcorr := correction_sum_low hm
  have hdelta := (weighted_delta_low hm).mul_left (inversePower 4)
  have hcorr' := hcorr.trans
    (hdelta.sub (LowEq.refl m
      (PowerSeries.C ℤ (Nat.choose (m+1) 2 : ℤ) * PowerSeries.X^(m-1))))
  have he : inversePower 4 * ((1-PowerSeries.X)*inversePochhammer (m-1)) =
      inversePower 3 * inversePochhammer (m-1) := by
    rw [← mul_assoc, inversePower_four_mul_one_sub]
  rw [he] at hcorr'
  have h := (Y_low hm).sub hcorr'
  have heq : (reversedCorrection m : PowerSeries ℤ) =
      (Y m : PowerSeries ℤ) -
      (∑ r ∈ Finset.range m, PowerSeries.X^r * (H (m-r) : PowerSeries ℤ) *
        (delta (2*m+1) r : PowerSeries ℤ)) := by
    have hc : ((∑ r ∈ Finset.range (m-1), X^r * H (m-r) * delta (2*m+1) r : ℤ[X]) :
        PowerSeries ℤ) = ∑ r ∈ Finset.range (m-1),
        ((X^r * H (m-r) * delta (2*m+1) r : ℤ[X]) : PowerSeries ℤ) := by
      simpa only [Polynomial.coeToPowerSeries.ringHom_apply] using
        (map_sum Polynomial.coeToPowerSeries.ringHom
          (fun r => X^r * H (m-r) * delta (2*m+1) r) (Finset.range (m-1)))
    simp only [reversedCorrection, Polynomial.coe_sub, hc,
      Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
    rw [correction_sum_extend hm]
  rw [heq]
  convert h using 1 <;> ring

/-- All lower coefficients of the reversed correction vanish. -/
theorem reversedCorrection_coeff_below {m k : ℕ} (hm : 1 ≤ m) (hk : k < m-1) :
    (reversedCorrection m).coeff k = 0 := by
  have h := reversedCorrection_low hm k (by omega)
  simpa only [Polynomial.coeff_coe, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, if_neg (show k ≠ m-1 by omega), mul_zero] using h

/-- The first surviving coefficient is the manuscript's binomial value. -/
theorem reversedCorrection_coeff_critical {m : ℕ} (hm : 1 ≤ m) :
    (reversedCorrection m).coeff (m-1) = (Nat.choose (m+1) 2 : ℤ) := by
  have h := reversedCorrection_low hm (m-1) (by omega)
  simpa only [Polynomial.coeff_coe, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, if_pos rfl, ite_true, mul_one] using h

end Guralnick.Gaussian
