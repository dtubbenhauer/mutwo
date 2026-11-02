import Guralnick.GaussianReversal

/-!
# Gaussian reciprocity from q-Pascal, and unconditional cancellation

The adjacent-binomial relation gives the second q-Pascal recursion. Reversal
then interchanges the two recursions. This discharges the general reciprocity
input to the preceding file, without importing any mathematical assumption.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.Gaussian

/-- The adjacent Gaussian-binomial relation, proved uniformly by q-Pascal. -/
theorem qBinomial_adjacent {n k : ℕ} (hk : k ≤ n) :
    (1-X^(k+1))*qBinomial n (k+1) = (1-X^(n-k))*qBinomial n k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    cases k with
    | zero =>
      simp only [qBinomial_succ_succ, qBinomial_zero_right, Nat.sub_zero,
        zero_add, pow_one, mul_one]
      have h := ih (k := 0) (Nat.zero_le n)
      simp only [qBinomial_zero_right, Nat.sub_zero, zero_add, pow_one, mul_one] at h
      rw [pow_succ]
      linear_combination X * h
    | succ k =>
      by_cases hnext : k+1 ≤ n
      · have h₁ := ih hnext
        have h₀ := ih (k := k) (by omega : k ≤ n)
        have hp : (X : ℤ[X])^(k+2) * X^(n-(k+1)) = X^(k+1) * X^(n-k) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        simp only [qBinomial_succ_succ, Nat.add_sub_add_right]
        calc
          (1-X^(k+1+1)) * (qBinomial n (k+1) + X^(k+1+1)*qBinomial n (k+1+1)) =
              (1-X^(k+1+1))*qBinomial n (k+1) +
              X^(k+1+1)*((1-X^(k+1+1))*qBinomial n (k+1+1)) := by ring
          _ = (1-X^(k+1+1))*qBinomial n (k+1) +
              X^(k+1+1)*((1-X^(n-(k+1)))*qBinomial n (k+1)) := by rw [h₁]
          _ = (1-X^(n-k))*qBinomial n k +
              X^(k+1)*((1-X^(n-k))*qBinomial n (k+1)) := by
            rw [← h₀]
            linear_combination -qBinomial n (k+1) * hp
          _ = (1-X^(n-k)) * (qBinomial n k + X^(k+1)*qBinomial n (k+1)) := by ring
      · have he : k = n := by omega
        subst k
        rw [qBinomial_eq_zero (by omega : n+1 < n+1+1)]
        simp only [Nat.sub_self, pow_zero, sub_self, zero_mul, mul_zero]

/-- The other q-Pascal recursion. -/
theorem qBinomial_other_pascal {n k : ℕ} (hk : k ≤ n) :
    qBinomial (n+1) (k+1) = X^(n-k)*qBinomial n k + qBinomial n (k+1) := by
  rw [qBinomial_succ_succ]
  have h := qBinomial_adjacent hk
  linear_combination -h

/-- Gaussian reciprocity is proved for the actual recursively defined
polynomials. No positivity, symmetry or polynomial formula is postulated. -/
theorem qBinomial_reflect {n k : ℕ} (hk : k ≤ n) :
    Polynomial.reflect (k*(n-k)) (qBinomial n k) = qBinomial n k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases hnext : k+1 ≤ n
      · have hk₀ : k ≤ n := by omega
        have he₀ : (k+1)*(n+1-(k+1)) = (n-k)+k*(n-k) := by
          rw [Nat.add_sub_add_right]
          ring
        have he₁ : (k+1)*(n+1-(k+1)) = (k+1)+(k+1)*(n-(k+1)) := by
          have he : n-k = (n-(k+1))+1 := by omega
          rw [Nat.add_sub_add_right, he]
          ring
        rw [qBinomial_succ_succ, reflect_add]
        have hr₀ : Polynomial.reflect ((k+1)*(n+1-(k+1))) (qBinomial n k) =
            X^(n-k)*qBinomial n k := by
          rw [he₀, reflect_extend _ (qBinomial_natDegree hk₀).le, ih hk₀]
        have hr₁ : Polynomial.reflect ((k+1)*(n+1-(k+1)))
            (X^(k+1)*qBinomial n (k+1)) = qBinomial n (k+1) := by
          rw [he₁, Polynomial.reflect_mul _ _ (natDegree_X_pow_le _)
            (qBinomial_natDegree hnext).le]
          simp only [reflect_monomial, revAt_le le_rfl, Nat.sub_self,
            pow_zero, one_mul, ih hnext]
        rw [hr₀, hr₁]
        exact (qBinomial_other_pascal hk₀).symm
      · have he : k = n := by omega
        subst k
        simp only [qBinomial_succ_succ, qBinomial_eq_zero (by omega : n < n+1),
          mul_zero, add_zero, Nat.sub_self, mul_zero]
        simpa using ih (k := n) le_rfl

/-- The previously isolated literature input is now discharged. -/
theorem gaussianReciprocity : GaussianReciprocity := fun _ _ hk => qBinomial_reflect hk

/-- The complete Gaussian cancellation lemma is kernel proved with no
external mathematical hypotheses. This is the actual `Q_m` of the paper. -/
theorem gaussian_cancellation {m : ℕ} (hm : 2 ≤ m) :
    (Q m).natDegree ≤ criticalDegree m ∧
      (Q m).coeff (criticalDegree m) = (Nat.choose (m+1) 2 : ℤ) :=
  cancellation gaussianReciprocity hm

end Guralnick.Gaussian
