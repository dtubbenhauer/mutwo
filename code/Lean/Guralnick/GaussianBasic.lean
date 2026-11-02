import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# The polynomials in the manuscript's Gaussian cancellation

These are actual integer polynomials. In particular, `qBinomial` is defined
by the usual q-Pascal recursion, not by the desired cancellation identity.
The lower index in `difference` has a separate zero branch; it is never
silently replaced by truncated natural subtraction.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Guralnick.Gaussian

/-- Gaussian binomial polynomial, with zero outside its natural range. -/
def qBinomial : ℕ → ℕ → ℤ[X]
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => qBinomial n k + X ^ (k + 1) * qBinomial n (k + 1)

@[simp] theorem qBinomial_zero_right (n : ℕ) : qBinomial n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qBinomial_zero_succ (k : ℕ) : qBinomial 0 (k+1) = 0 := rfl

@[simp] theorem qBinomial_succ_succ (n k : ℕ) :
    qBinomial (n+1) (k+1) = qBinomial n k + X^(k+1)*qBinomial n (k+1) := rfl

theorem qBinomial_eq_zero {n k : ℕ} (h : n < k) : qBinomial n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => simp [ih (by omega : n < k), ih (by omega : n < k+1)]

theorem qBinomial_const {n k : ℕ} (h : k ≤ n) : (qBinomial n k).coeff 0 = 1 := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [qBinomial_succ_succ, coeff_add, coeff_X_pow_mul']
      simp [ih (by omega : k ≤ n)]

/-- Exact degree and leading coefficient of every nonzero Gaussian
polynomial, proved by the defining q-Pascal recursion. -/
theorem qBinomial_degree_monic {n k : ℕ} (hk : k ≤ n) :
    (qBinomial n k).natDegree = k*(n-k) ∧ (qBinomial n k).Monic := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hkn : k ≤ n := by omega
      obtain ⟨hd₀, hm₀⟩ := ih hkn
      by_cases hnext : k+1 ≤ n
      · obtain ⟨hd₁, hm₁⟩ := ih hnext
        have hmulmonic : (X^(k+1) * qBinomial n (k+1)).Monic :=
          (monic_X_pow (k+1)).mul hm₁
        have hd₂ : (X^(k+1) * qBinomial n (k+1)).natDegree = (k+1)*(n-k) := by
          rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hm₁.ne_zero,
            natDegree_X_pow, hd₁]
          have he : n-k = (n-(k+1))+1 := by omega
          rw [he]
          ring
        have hlt : (qBinomial n k).natDegree <
            (X^(k+1) * qBinomial n (k+1)).natDegree := by
          rw [hd₀, hd₂]
          have hp : 0 < n-k := by omega
          nlinarith
        rw [qBinomial_succ_succ]
        constructor
        · rw [natDegree_add_eq_right_of_natDegree_lt hlt, hd₂]
          congr 1
          omega
        · exact (leadingCoeff_add_of_degree_lt (degree_lt_degree hlt)).trans hmulmonic
      · have he : k = n := by omega
        subst k
        simp only [qBinomial_succ_succ, qBinomial_eq_zero (by omega : n < n+1),
          mul_zero, add_zero, Nat.sub_self, mul_zero]
        exact ⟨by simpa using hd₀, hm₀⟩

theorem qBinomial_natDegree {n k : ℕ} (hk : k ≤ n) :
    (qBinomial n k).natDegree = k*(n-k) := (qBinomial_degree_monic hk).1

theorem qBinomial_monic {n k : ℕ} (hk : k ≤ n) :
    (qBinomial n k).Monic := (qBinomial_degree_monic hk).2

/-- `[l]_q`. -/
def qInteger (l : ℕ) : ℤ[X] := ∑ t ∈ Finset.range l, X^t

theorem qInteger_coeff (l k : ℕ) : (qInteger l).coeff k = if k < l then 1 else 0 := by
  simp only [qInteger, finset_sum_coeff, coeff_X_pow]
  by_cases hk : k < l
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [Ne.symm hbk]
    · intro h
      exact (h (Finset.mem_range.mpr hk)).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro b hb
    have hb' := Finset.mem_range.mp hb
    simp [show k ≠ b by omega]

theorem qInteger_natDegree {l : ℕ} (hl : 1 ≤ l) : (qInteger l).natDegree = l-1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold qInteger
    apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [natDegree_X_pow]
    have hi' := Finset.mem_range.mp hi
    omega
  · rw [qInteger_coeff, if_pos (by omega : l-1 < l)]
    norm_num

theorem qInteger_monic {l : ℕ} (hl : 1 ≤ l) : (qInteger l).Monic := by
  rw [Monic, leadingCoeff, qInteger_natDegree hl, qInteger_coeff,
    if_pos (by omega : l-1 < l)]

/-- The explicit symmetric correction polynomial; `H 1 = 0`. -/
def H (l : ℕ) : ℤ[X] :=
  ∑ t ∈ Finset.range (l-1), C (Nat.choose (t+3) 3 : ℤ) * (X^t + X^(2*l-3-t))

/-- The polynomial called `M_l` in the manuscript. -/
def M (l : ℕ) : ℤ[X] := X^(l*l) * H l

/-- `G(n,r)-G(n,r-1)`, with the negative lower index interpreted as zero. -/
def delta (n : ℕ) : ℕ → ℤ[X]
  | 0 => qBinomial n 0
  | r+1 => qBinomial n (r+1) - qBinomial n r

/-- The full-spherical standard coefficient `R_(n,r)`. -/
def difference (n : ℕ) : ℕ → ℤ[X]
  | 0 => qBinomial n 0
  | r+1 => qBinomial n (r+1) - X^(n-2*(r+1)+1)*qBinomial n r

/-- The uncorrected lower-standard polynomial. -/
def Y (m : ℕ) : ℤ[X] := qInteger m ^ 3 * qBinomial (2*m-1) (m-1)

/-- The actual polynomial `Q_m` in the manuscript. -/
def Q (m : ℕ) : ℤ[X] :=
  Y m - ∑ r ∈ Finset.range (m-1), M (m-r) * difference (2*m+1) r

/-- Reversal degree of the uncorrected polynomial. -/
def topDegree (m : ℕ) : ℕ := m*m + 2*m - 3

/-- Critical degree after correction. -/
def criticalDegree (m : ℕ) : ℕ := m*(m+1)-2

@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem M_one : M 1 = 0 := by simp [M]
@[simp] theorem delta_zero (n : ℕ) : delta n 0 = 1 := by simp [delta]
@[simp] theorem difference_zero (n : ℕ) : difference n 0 = 1 := by simp [difference]

theorem delta_const {n r : ℕ} (h : r ≤ n) :
    (delta n r).coeff 0 = if r = 0 then 1 else 0 := by
  cases r with
  | zero => simp
  | succ r => simp [delta, qBinomial_const h, qBinomial_const (by omega : r ≤ n)]

/-- Equality of coefficients in all degrees strictly below `d`. -/
def LowEq (d : ℕ) (f g : PowerSeries ℤ) : Prop :=
  ∀ k < d, PowerSeries.coeff ℤ k f = PowerSeries.coeff ℤ k g

namespace LowEq

theorem refl (d : ℕ) (f : PowerSeries ℤ) : LowEq d f f := fun _ _ => rfl

theorem symm {d : ℕ} {f g : PowerSeries ℤ} (h : LowEq d f g) : LowEq d g f :=
  fun k hk => (h k hk).symm

theorem trans {d : ℕ} {f g h : PowerSeries ℤ} (hfg : LowEq d f g)
    (hgh : LowEq d g h) : LowEq d f h := fun k hk => (hfg k hk).trans (hgh k hk)

theorem mono {d e : ℕ} {f g : PowerSeries ℤ} (h : LowEq d f g) (he : e ≤ d) :
    LowEq e f g := fun k hk => h k (lt_of_lt_of_le hk he)

theorem add {d : ℕ} {f g a b : PowerSeries ℤ} (hfg : LowEq d f g)
    (hab : LowEq d a b) : LowEq d (f+a) (g+b) := by
  intro k hk
  simp only [map_add, hfg k hk, hab k hk]

theorem sub {d : ℕ} {f g a b : PowerSeries ℤ} (hfg : LowEq d f g)
    (hab : LowEq d a b) : LowEq d (f-a) (g-b) := by
  intro k hk
  simp only [map_sub, hfg k hk, hab k hk]

theorem mul {d : ℕ} {f g a b : PowerSeries ℤ} (hfg : LowEq d f g)
    (hab : LowEq d a b) : LowEq d (f*a) (g*b) := by
  intro k hk
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hh := Finset.mem_antidiagonal.mp hij
  rw [hfg ij.1 (by omega), hab ij.2 (by omega)]

theorem mul_left {d : ℕ} {f g : PowerSeries ℤ} (h : LowEq d f g)
    (a : PowerSeries ℤ) : LowEq d (a*f) (a*g) := (refl d a).mul h

theorem mul_right {d : ℕ} {f g : PowerSeries ℤ} (h : LowEq d f g)
    (a : PowerSeries ℤ) : LowEq d (f*a) (g*a) := h.mul (refl d a)

theorem pow {d : ℕ} {f g : PowerSeries ℤ} (h : LowEq d f g) (n : ℕ) :
    LowEq d (f^n) (g^n) := by
  induction n with
  | zero => exact refl d 1
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem sum {ι : Type*} (s : Finset ι) {d : ℕ} {f g : ι → PowerSeries ℤ}
    (h : ∀ i ∈ s, LowEq d (f i) (g i)) : LowEq d (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro k hk
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi k hk)

theorem shift {d : ℕ} {f g : PowerSeries ℤ} (h : LowEq d f g) (r : ℕ) :
    LowEq (r+d) (PowerSeries.X^r*f) (PowerSeries.X^r*g) := by
  intro k hk
  simp only [PowerSeries.coeff_X_pow_mul']
  split_ifs with hr
  · exact h (k-r) (by omega)
  · rfl

end LowEq

/-- The coefficients of `(1-q)^(-d)`, supplied by a theorem already in mathlib. -/
def inversePower (d : ℕ) : PowerSeries ℤ := (PowerSeries.invOneSubPow ℤ d).val

theorem inversePower_four_coeff (k : ℕ) :
    PowerSeries.coeff ℤ k (inversePower 4) = (Nat.choose (k+3) 3 : ℤ) := by
  simp [inversePower, PowerSeries.invOneSubPow, PowerSeries.coeff_mk, Nat.add_comm]

theorem inversePower_add (a b : ℕ) :
    inversePower (a+b) = inversePower a * inversePower b := by
  simp [inversePower, PowerSeries.invOneSubPow_add]

/-- Before its middle degree, only the first half of the symmetric correction
contributes. This is a coefficient computation, not a truncation assumption. -/
theorem H_coeff_before {l k : ℕ} (hl : 1 ≤ l) (hk : k < l-1) :
    (H l).coeff k = (Nat.choose (k+3) 3 : ℤ) := by
  unfold H
  simp only [finset_sum_coeff, coeff_C_mul, coeff_add, coeff_X_pow]
  have hz : ∀ t ∈ Finset.range (l-1), k ≠ 2*l-3-t := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    omega
  rw [Finset.sum_eq_single k]
  · simp [hz k (Finset.mem_range.mpr hk)]
  · intro b hb hbk
    simp only [if_neg (Ne.symm hbk), if_neg (hz b hb), zero_add, mul_zero]
  · intro hk'
    exact (hk' (Finset.mem_range.mpr hk)).elim

/-- At the middle degree the second half contributes its first term. -/
theorem H_coeff_middle {l : ℕ} (hl : 2 ≤ l) :
    (H l).coeff (l-1) = (Nat.choose (l+1) 3 : ℤ) := by
  unfold H
  simp only [finset_sum_coeff, coeff_C_mul, coeff_add, coeff_X_pow]
  have hfirst : ∀ t ∈ Finset.range (l-1), l-1 ≠ t := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    omega
  rw [Finset.sum_eq_single (l-2)]
  · have h₁ : l-1 ≠ l-2 := by omega
    have h₂ : l-1 = 2*l-3-(l-2) := by omega
    have h₃ : l-2+3 = l+1 := by omega
    simp only [if_neg h₁, if_pos h₂, h₃, zero_add, mul_one]
  · intro b hb hbl
    have hb' := Finset.mem_range.mp hb
    have h₂ : l-1 ≠ 2*l-3-b := by omega
    simp [hfirst b hb, h₂]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- The manuscript's truncation defect, including `l=1`. -/
theorem H_low {l : ℕ} (hl : 1 ≤ l) :
    LowEq l (H l : PowerSeries ℤ)
      (inversePower 4 - PowerSeries.C ℤ (Nat.choose (l+1) 2 : ℤ) *
        PowerSeries.X^(l-1)) := by
  intro k hk
  rw [Polynomial.coeff_coe, map_sub, inversePower_four_coeff,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases hk' : k < l-1
  · rw [H_coeff_before hl hk', if_neg (by omega)]
    ring
  · have hke : k = l-1 := by omega
    subst k
    rw [if_pos rfl, mul_one]
    by_cases hl' : l = 1
    · subst l
      norm_num
    · rw [H_coeff_middle (by omega)]
      have hidx : l-1+3 = (l+1)+1 := by omega
      rw [hidx, Nat.choose_succ_succ' (l+1) 2, Nat.cast_add]
      ring

/-- Shifting the preceding defect gives the exact local congruence used in
the manuscript's sum, with no loss at `r=m-1`. -/
theorem shifted_H_low {m r : ℕ} (hr : r < m) :
    LowEq m (PowerSeries.X^r * (H (m-r) : PowerSeries ℤ))
      (PowerSeries.X^r * inversePower 4 -
        PowerSeries.C ℤ (Nat.choose (m-r+1) 2 : ℤ) * PowerSeries.X^(m-1)) := by
  have h := (H_low (l := m-r) (by omega)).shift r
  have hsum : r+(m-r) = m := by omega
  have hexp : r+(m-r-1) = m-1 := by omega
  rw [hsum] at h
  convert h using 1 <;> try rfl
  simp only [mul_sub]
  rw [mul_left_comm, ← pow_add, hexp]


end Guralnick.Gaussian
