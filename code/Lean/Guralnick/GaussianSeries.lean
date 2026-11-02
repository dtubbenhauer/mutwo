import Guralnick.GaussianBasic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Finite q-series identities behind the cancellation

`inversePochhammer n` is the actual inverse of the finite product
`∏ i=1,...,n (1-X^i)` in integer power series. Its finite Euler identity
is proved directly. Gaussian asymptotics are proved from the defining q-Pascal recursion.
No external or family-specific cancellation hypothesis is used.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.Gaussian

namespace LowEq

theorem prod {ι : Type*} (s : Finset ι) {d : ℕ} {f g : ι → PowerSeries ℤ}
    (h : ∀ i ∈ s, LowEq d (f i) (g i)) : LowEq d (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using refl d 1
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem X_pow_zero {d n : ℕ} (h : d ≤ n) :
    LowEq d ((PowerSeries.X : PowerSeries ℤ)^n) 0 := by
  intro k hk
  simp [PowerSeries.coeff_X_pow, show k ≠ n by omega]

theorem shift_zero (d : ℕ) (f : PowerSeries ℤ) :
    LowEq d (PowerSeries.X^d*f) 0 := by
  simpa using (X_pow_zero (d := d) (n := d) le_rfl).mul_right f

end LowEq

/-- Finite q-Pochhammer product. -/
def pochhammer (n : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range n, (1-PowerSeries.X^(i+1))

@[simp] theorem pochhammer_zero : pochhammer 0 = 1 := by simp [pochhammer]

theorem pochhammer_succ (n : ℕ) :
    pochhammer (n+1) = pochhammer n * (1-PowerSeries.X^(n+1)) := by
  simp [pochhammer, Finset.prod_range_succ]

@[simp] theorem pochhammer_constant (n : ℕ) :
    PowerSeries.constantCoeff ℤ (pochhammer n) = 1 := by
  simp [pochhammer]

/-- Inverse of the explicitly defined finite Pochhammer product. -/
def inversePochhammer (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (pochhammer n) 1

@[simp] theorem pochhammer_mul_inverse (n : ℕ) :
    pochhammer n * inversePochhammer n = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp

@[simp] theorem inverse_mul_pochhammer (n : ℕ) :
    inversePochhammer n * pochhammer n = 1 := by
  rw [mul_comm]
  exact pochhammer_mul_inverse n

@[simp] theorem inversePochhammer_zero : inversePochhammer 0 = 1 := by
  have h := pochhammer_mul_inverse 0
  simpa using h

/-- Removing the last factor of the denominator. -/
theorem inversePochhammer_step (n : ℕ) :
    inversePochhammer (n+1) * (1-PowerSeries.X^(n+1)) = inversePochhammer n := by
  calc
    _ = inversePochhammer n * pochhammer (n+1) * inversePochhammer (n+1) := by
      rw [pochhammer_succ]
      calc
        _ = (inversePochhammer n * pochhammer n) *
            (inversePochhammer (n+1) * (1-PowerSeries.X^(n+1))) := by rw [inverse_mul_pochhammer]; simp
        _ = _ := by ring
    _ = _ := by rw [mul_assoc, pochhammer_mul_inverse]; simp

/-- Finite Euler telescoping, stronger than the truncated identity needed
in the manuscript. No infinite products or convergence assumptions occur. -/
theorem finite_euler (n : ℕ) :
    (∑ r ∈ Finset.range (n+1), PowerSeries.X^r * inversePochhammer r) =
      inversePochhammer n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := inversePochhammer_step n
    rw [← h]
    ring

/-- Uniform Gaussian asymptotics proved from q-Pascal recursion. The shifted
second term gains enough degree to use the induction hypothesis; the
outside-range boundary is handled separately. -/
theorem qBinomial_low_full {n k : ℕ} (hk : k ≤ n) :
    LowEq (n-k+1) (qBinomial n k : PowerSeries ℤ) (inversePochhammer k) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp only [qBinomial_zero_right, Polynomial.coe_one, inversePochhammer_zero]
    exact LowEq.refl _ _
  | succ n ih =>
    cases k with
    | zero =>
      simp only [qBinomial_zero_right, Polynomial.coe_one, inversePochhammer_zero]
      exact LowEq.refl _ _
    | succ k =>
      have hkn : k ≤ n := by omega
      have hfirst := ih hkn
      have hsecond : LowEq (n-k+1)
          (PowerSeries.X^(k+1)*(qBinomial n (k+1) : PowerSeries ℤ))
          (PowerSeries.X^(k+1)*inversePochhammer (k+1)) := by
        by_cases hnext : k+1 ≤ n
        · exact ((ih hnext).shift (k+1)).mono (by omega)
        · have hzero := qBinomial_eq_zero (n := n) (k := k+1) (by omega)
          rw [hzero, Polynomial.coe_zero, mul_zero]
          simpa using ((LowEq.X_pow_zero (by omega : n-k+1 ≤ k+1)).mul_right
            (inversePochhammer (k+1))).symm
      have hsum := hfirst.add hsecond
      have he : inversePochhammer k + PowerSeries.X^(k+1)*inversePochhammer (k+1) =
          inversePochhammer (k+1) := by
        rw [← inversePochhammer_step k]
        ring
      simpa only [qBinomial_succ_succ, Polynomial.coe_add, Polynomial.coe_mul,
        Polynomial.coe_pow, Polynomial.coe_X, Nat.add_sub_add_right, he] using hsum

/-- A convenient weakening of the full Gaussian asymptotic theorem. -/
theorem qBinomial_low {n k d : ℕ} (hk : k ≤ n) (hd : d ≤ n-k+1) :
    LowEq d (qBinomial n k : PowerSeries ℤ) (inversePochhammer k) :=
  (qBinomial_low_full hk).mono hd

/-- Low coefficients of `[m]_q` agree with `(1-q)^(-1)`. -/
theorem qInteger_low (m : ℕ) : LowEq m (qInteger m : PowerSeries ℤ) (inversePower 1) := by
  intro k hk
  rw [Polynomial.coeff_coe]
  simp only [qInteger, finset_sum_coeff, coeff_X_pow]
  rw [Finset.sum_eq_single k]
  · simp [inversePower, PowerSeries.invOneSubPow, PowerSeries.coeff_mk]
  · intro b hb hbk
    simp [Ne.symm hbk]
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

theorem inversePower_one_cube : inversePower 1 ^ 3 = inversePower 3 := by
  have h := inversePower_add 1 1
  have h' := inversePower_add 2 1
  norm_num at h h'
  rw [h', h]
  ring

theorem Y_low {m : ℕ} (hm : 1 ≤ m) :
    LowEq m (Y m : PowerSeries ℤ) (inversePower 3 * inversePochhammer (m-1)) := by
  have h := ((qInteger_low m).pow 3).mul
    (qBinomial_low (n := 2*m-1) (k := m-1) (d := m) (by omega) (by omega))
  simpa only [Y, Polynomial.coe_mul, Polynomial.coe_pow, inversePower_one_cube] using h

/-- The finite weighted Gaussian sum has the same low coefficients as the
finite Euler sum. -/
theorem weighted_qBinomial_low {m : ℕ} (hm : 1 ≤ m) :
    LowEq m (∑ r ∈ Finset.range m, PowerSeries.X^r *
      (qBinomial (2*m+1) r : PowerSeries ℤ)) (inversePochhammer (m-1)) := by
  have h := LowEq.sum (Finset.range m)
    (fun r hr => (qBinomial_low (n := 2*m+1) (k := r) (d := m)
      (by have := Finset.mem_range.mp hr; omega)
      (by have := Finset.mem_range.mp hr; omega)).mul_left (PowerSeries.X^r))
  have heuler : (∑ r ∈ Finset.range m, PowerSeries.X^r * inversePochhammer r) =
      inversePochhammer (m-1) := by
    simpa only [Nat.sub_add_cancel hm] using finite_euler (m-1)
  simpa only [heuler] using h

end Guralnick.Gaussian
