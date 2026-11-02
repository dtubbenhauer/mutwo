import Guralnick.GaussianCancellation

/-!
# Reversal of the actual Gaussian correction

The general reciprocity theorem is isolated as an argument in this file;
`GaussianReciprocity.lean` proves it from q-Pascal and discharges that argument.
Every degree bound and every identity specializing reversal to the
manuscript's correction is proved here.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.Gaussian

/-- Statement of standard Gaussian reciprocity for the independently defined
q-Pascal polynomials. It is proved in `GaussianReciprocity.lean`. -/
def GaussianReciprocity : Prop :=
  ∀ n k : ℕ, k ≤ n →
    Polynomial.reflect (k*(n-k)) (qBinomial n k) = qBinomial n k

theorem reflect_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (d : ℕ) :
    Polynomial.reflect d (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect d (f i) := by
  ext k
  simp only [coeff_reflect, finset_sum_coeff]

/-- Enlarging the reversal degree contributes the corresponding power of X. -/
theorem reflect_extend (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d) (r : ℕ) :
    Polynomial.reflect (r+d) p = X^r * Polynomial.reflect d p := by
  simpa only [one_mul, reflect_one] using
    Polynomial.reflect_mul (1 : ℤ[X]) p (by simp : (1 : ℤ[X]).natDegree ≤ r) hd

theorem H_natDegree_le (l : ℕ) : (H l).natDegree ≤ 2*l-3 := by
  unfold H
  apply natDegree_sum_le_of_forall_le
  intro t ht
  have ht' := Finset.mem_range.mp ht
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_add_le_of_degree_le
  · rw [natDegree_X_pow]
    omega
  · rw [natDegree_X_pow]
    omega

theorem H_reflect (l : ℕ) : Polynomial.reflect (2*l-3) (H l) = H l := by
  unfold H
  rw [reflect_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have htdeg : t ≤ 2*l-3 := by omega
  rw [reflect_C_mul, reflect_add, reflect_monomial, reflect_monomial,
    revAt_le htdeg, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self htdeg]
  ring

theorem qInteger_reflect {m : ℕ} (hm : 1 ≤ m) :
    Polynomial.reflect (m-1) (qInteger m) = qInteger m := by
  ext k
  rw [coeff_reflect, qInteger_coeff, qInteger_coeff]
  by_cases hk : k ≤ m-1
  · rw [revAt_le hk]
    simp [show m-1-k < m by omega, show k < m by omega]
  · rw [revAt_eq_self_of_lt (by omega : m-1 < k)]

theorem reflect_pow_of_reflect (p : ℤ[X]) {d : ℕ}
    (hd : p.natDegree ≤ d) (href : Polynomial.reflect d p = p) (s : ℕ) :
    Polynomial.reflect (s*d) (p^s) = p^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.succ_mul, pow_succ,
      Polynomial.reflect_mul (p^s) p (natDegree_pow_le_of_le s hd) hd,
      ih, href]

theorem Y_natDegree {m : ℕ} (hm : 1 ≤ m) : (Y m).natDegree = topDegree m := by
  have hg : m-1 ≤ 2*m-1 := by omega
  have hq := qInteger_monic hm
  rw [Y, natDegree_mul (hq.pow 3).ne_zero (qBinomial_monic hg).ne_zero,
    natDegree_pow, qInteger_natDegree hm, qBinomial_natDegree hg]
  unfold topDegree
  have h₁ : m-1+1 = m := by omega
  have h₂ : 2*m-1-(m-1) = m := by omega
  rw [h₂]
  have h₃ : m*m+2*m-3+3 = m*m+2*m := Nat.sub_add_cancel (by nlinarith)
  nlinarith

theorem Y_reflect (hrec : GaussianReciprocity) {m : ℕ} (hm : 1 ≤ m) :
    Polynomial.reflect (topDegree m) (Y m) = Y m := by
  have hg : m-1 ≤ 2*m-1 := by omega
  have he : topDegree m = 3*(m-1) + (m-1)*(2*m-1-(m-1)) := by
    unfold topDegree
    have h₁ : m-1+1 = m := by omega
    have h₂ : 2*m-1-(m-1) = m := by omega
    rw [h₂]
    have h₃ : m*m+2*m-3+3 = m*m+2*m := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  unfold Y
  rw [he, Polynomial.reflect_mul _ _
      (natDegree_pow_le_of_le 3 (qInteger_natDegree hm).le)
      (qBinomial_natDegree hg).le,
    reflect_pow_of_reflect _ (qInteger_natDegree hm).le (qInteger_reflect hm),
    hrec _ _ hg]

theorem difference_degree_identity {n r : ℕ} (hr : 1 ≤ r) (hn : 2*r ≤ n) :
    (n-2*r+1) + (r-1)*(n-(r-1)) = r*(n-r) := by
  have h₁ : n-2*r+2*r = n := by omega
  have h₂ : r-1+1 = r := by omega
  have h₃ : n-(r-1)+(r-1) = n := by omega
  have h₄ : n-r+r = n := by omega
  nlinarith

theorem difference_natDegree_le {n r : ℕ} (hn : 2*r ≤ n) :
    (difference n r).natDegree ≤ r*(n-r) := by
  cases r with
  | zero => simp
  | succ r =>
    have hk : r+1 ≤ n := by omega
    have hk' : r ≤ n := by omega
    unfold difference
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (qBinomial_natDegree hk).le
    · apply natDegree_mul_le.trans
      rw [natDegree_X_pow, qBinomial_natDegree hk']
      have hh := difference_degree_identity (r := r+1) (by omega) hn
      simpa using hh.le

theorem difference_reflect (hrec : GaussianReciprocity) {n r : ℕ}
    (hn : 2*r ≤ n) :
    Polynomial.reflect (r*(n-r)) (difference n r) = delta n r := by
  cases r with
  | zero => simp
  | succ r =>
    have hk : r+1 ≤ n := by omega
    have hk' : r ≤ n := by omega
    have he := difference_degree_identity (r := r+1) (by omega) hn
    simp only [Nat.add_sub_cancel] at he
    rw [difference, reflect_sub, hrec _ _ hk]
    rw [← he, Polynomial.reflect_mul _ _ (natDegree_X_pow_le _)
      (qBinomial_natDegree hk').le]
    simp only [reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, one_mul,
      hrec _ _ hk', delta]

theorem M_natDegree_le (l : ℕ) : (M l).natDegree ≤ l*l+(2*l-3) := by
  apply natDegree_mul_le.trans
  rw [natDegree_X_pow]
  exact Nat.add_le_add_left (H_natDegree_le l) _

theorem M_reflect (l : ℕ) : Polynomial.reflect (l*l+(2*l-3)) (M l) = H l := by
  rw [M, Polynomial.reflect_mul _ _ (natDegree_X_pow_le _) (H_natDegree_le l)]
  simp only [reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, one_mul, H_reflect]

/-- The numerical degree identity supplying the residual `q^r` factor. -/
theorem summand_degree_identity {m r : ℕ} (hr : r < m-1) :
    r + ((m-r)*(m-r)+(2*(m-r)-3) + r*(2*m+1-r)) = topDegree m := by
  have h₁ : m-r+r = m := by omega
  have h₂ : 2*(m-r)-3+3 = 2*(m-r) := by omega
  have h₃ : 2*m+1-r+r = 2*m+1 := by omega
  have h₄ : m*m+2*m-3+3 = m*m+2*m := by omega
  unfold topDegree
  nlinarith

/-- Reverse one actual correction summand, with the full-spherical
Gaussian difference and the symmetric correction both retained. -/
theorem summand_reflect (hrec : GaussianReciprocity) {m r : ℕ} (hr : r < m-1) :
    Polynomial.reflect (topDegree m) (M (m-r) * difference (2*m+1) r) =
      X^r * H (m-r) * delta (2*m+1) r := by
  have hn : 2*r ≤ 2*m+1 := by omega
  have hd := natDegree_mul_le_of_le (M_natDegree_le (m-r)) (difference_natDegree_le hn)
  rw [← summand_degree_identity hr, reflect_extend _ hd,
    Polynomial.reflect_mul _ _ (M_natDegree_le (m-r)) (difference_natDegree_le hn),
    M_reflect, difference_reflect hrec hn]
  ring

/-- The explicit reversed correction really is the reversal of `Q_m`. -/
theorem Q_reflect (hrec : GaussianReciprocity) {m : ℕ} (hm : 2 ≤ m) :
    Polynomial.reflect (topDegree m) (Q m) = reversedCorrection m := by
  rw [Q, reflect_sub, Y_reflect hrec (by omega), reflect_sum]
  unfold reversedCorrection
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact summand_reflect hrec (Finset.mem_range.mp hr)

theorem Q_natDegree_le_top {m : ℕ} (hm : 2 ≤ m) : (Q m).natDegree ≤ topDegree m := by
  unfold Q
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (Y_natDegree (by omega)).le
  · apply natDegree_sum_le_of_forall_le
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have h := natDegree_mul_le_of_le (M_natDegree_le (m-r))
      (difference_natDegree_le (by omega : 2*r ≤ 2*m+1))
    have he := summand_degree_identity hr'
    omega

/-- Degree arithmetic connecting reversal to the original critical index. -/
theorem critical_degree_identity {m : ℕ} (hm : 2 ≤ m) :
    criticalDegree m + (m-1) = topDegree m := by
  unfold criticalDegree topDegree
  have h₁ : m-1+1 = m := by omega
  have h₂ : m*(m+1)-2+2 = m*(m+1) := Nat.sub_add_cancel (by nlinarith)
  have h₃ : m*m+2*m-3+3 = m*m+2*m := Nat.sub_add_cancel (by nlinarith)
  nlinarith

/-- The manuscript's Gaussian cancellation lemma, conditional only on
standard Gaussian reciprocity; no original conclusion is an input. -/
theorem cancellation (hrec : GaussianReciprocity) {m : ℕ} (hm : 2 ≤ m) :
    (Q m).natDegree ≤ criticalDegree m ∧
      (Q m).coeff (criticalDegree m) = (Nat.choose (m+1) 2 : ℤ) := by
  have he := critical_degree_identity hm
  have htop := Q_natDegree_le_top hm
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    by_cases hkt : k ≤ topDegree m
    · have hj : topDegree m-k < m-1 := by omega
      have hz := reversedCorrection_coeff_below (m := m) (by omega) hj
      rw [← Q_reflect hrec hm, coeff_reflect, revAt_le (Nat.sub_le _ _),
        Nat.sub_sub_self hkt] at hz
      exact hz
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt htop (by omega))
  · have hh := reversedCorrection_coeff_critical (m := m) (by omega)
    rw [← Q_reflect hrec hm, coeff_reflect, revAt_le (by omega : m-1 ≤ topDegree m)] at hh
    have hidx : topDegree m-(m-1) = criticalDegree m := by omega
    simpa only [hidx] using hh

end Guralnick.Gaussian
