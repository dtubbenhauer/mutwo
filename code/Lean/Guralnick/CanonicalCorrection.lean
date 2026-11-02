import Guralnick.Positivity
import Mathlib.Tactic

/-!
# The descending canonical correction

This file proves the algebraic mechanism in Section 8, on genuine Laurent
polynomials: a bar-invariant coefficient is determined by its nonpositive
powers, and an upper-triangular family of such coefficients can be recovered
by descending induction. The explicit `correction` is the paper's `g_l`.

The triangular expansion and the positivity of the residual *standard*
coordinates remain explicit input to the generic descending theorem. They
are not identified as literature results or silently inferred from the
form of the correction. Instantiating them for the six-map web requires
the gallery and canonical-support arguments elsewhere in the manuscript.
-/

noncomputable section

namespace Guralnick.CanonicalCorrection

open scoped BigOperators
open Positivity

/-- A bar-invariant Laurent polynomial is determined by exponents at most
zero. This is the precise uniqueness used in the descending correction. -/
theorem eq_of_nonpositive {p q : LP}
    (hp : BarSymmetric p) (hq : BarSymmetric q)
    (h : ∀ n : ℤ, n ≤ 0 → p n = q n) : p = q := by
  apply LaurentPolynomial.ext
  intro n
  by_cases hn : n ≤ 0
  · exact h n hn
  · rw [← bar_coeff hp n, ← bar_coeff hq n]
    exact h (-n) (by omega)

/-- The difference of two bar-invariant polynomials cannot have only
strictly positive powers unless it is zero. -/
theorem eq_of_positive_difference {p q : LP}
    (hp : BarSymmetric p) (hq : BarSymmetric q)
    (h : LowerBound (p - q) 1) : p = q := by
  apply eq_of_nonpositive hp hq
  intro n hn
  have hzero := h n (by omega)
  change p n - q n = 0 at hzero
  omega

theorem lowerBound_add {p q : LP} {a : ℤ}
    (hp : LowerBound p a) (hq : LowerBound q a) : LowerBound (p + q) a := by
  intro n hn
  change p n + q n = 0
  rw [hp n hn, hq n hn, add_zero]

theorem lowerBound_sub {p q : LP} {a : ℤ}
    (hp : LowerBound p a) (hq : LowerBound q a) : LowerBound (p - q) a := by
  intro n hn
  change p n - q n = 0
  rw [hp n hn, hq n hn, sub_self]

theorem lowerBound_sum {ι : Type*} (s : Finset ι) (p : ι → LP) {a : ℤ}
    (h : ∀ i ∈ s, LowerBound (p i) a) : LowerBound (∑ i ∈ s, p i) a := by
  intro n hn
  change coeffHom n (∑ i ∈ s, p i) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => h i hi n hn)

theorem lowerBound_mono {p : LP} {a b : ℤ}
    (hp : LowerBound p a) (hab : b ≤ a) : LowerBound p b := by
  intro n hn
  exact hp n (lt_of_lt_of_le hn hab)

/-- The paper's explicit full-spherical correction. The `l=1` range is
empty, so the exceptional endpoint is zero without natural-subtraction
ambiguity in any Gaussian lower index. -/
def correction (l : ℕ) : LP :=
  ∑ t ∈ Finset.range (l - 1),
    LaurentPolynomial.C (Nat.choose (t + 3) 3 : ℤ) *
      (LaurentPolynomial.T (2 * (l : ℤ) - 3 - 2 * t) +
       LaurentPolynomial.T (-(2 * (l : ℤ) - 3 - 2 * t)))

@[simp] theorem correction_zero : correction 0 = 0 := by simp [correction]
@[simp] theorem correction_one : correction 1 = 0 := by simp [correction]

theorem correction_bar (l : ℕ) : BarSymmetric (correction l) := by
  unfold BarSymmetric correction
  simp only [map_sum, map_mul, map_add, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T, neg_neg]
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg (fun z : LP => LaurentPolynomial.C _ * z) (add_comm _ _)

theorem correction_two : correction 2 =
    LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) := by
  norm_num [correction, Finset.sum_range_succ]

theorem correction_three : correction 3 =
    LaurentPolynomial.T 3 + LaurentPolynomial.C 4 * LaurentPolynomial.T 1 +
    LaurentPolynomial.C 4 * LaurentPolynomial.T (-1) + LaurentPolynomial.T (-3) := by
  norm_num [correction, Finset.sum_range_succ]
  ring

/-- The correction's support bound, proved from its actual finite sum. -/
theorem correction_lowerBound (l : ℕ) (hl : 2 ≤ l) :
    LowerBound (correction l) (3 - 2 * l) := by
  apply lowerBound_sum
  intro t ht
  have ht' : t < l - 1 := Finset.mem_range.mp ht
  have hexp : 1 ≤ 2 * (l : ℤ) - 3 - 2 * t := by omega
  have hexp' : 2 * (l : ℤ) - 3 - 2 * t ≤ 2 * l - 3 := by omega
  intro n hn
  simp only [mul_add, ← LaurentPolynomial.single_eq_C_mul_T,
    coeff_add, Finsupp.single_apply]
  split_ifs <;> omega

theorem correction_constant (l : ℕ) : correction l 0 = 0 := by
  unfold correction
  change coeffHom 0 (∑ t ∈ Finset.range (l - 1), _) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have hexp : 1 ≤ 2 * (l : ℤ) - 3 - 2 * t := by omega
  change (LaurentPolynomial.C _ * _) 0 = 0
  simp only [mul_add, ← LaurentPolynomial.single_eq_C_mul_T,
    coeff_add, Finsupp.single_apply]
  split_ifs <;> omega

/-- A finite triangular coefficient system. Its diagonal is one; the term
indexed by `s` can affect only standard rows `r <= s`. This definition
records an actual expansion of Laurent coordinates, not KL semantics. -/
def triangularExpansion (n : ℕ) (h : ℕ → ℕ → LP) (a : ℕ → LP) (r : ℕ) : LP :=
  a r + ∑ s ∈ (Finset.range n).filter (r < ·), a s * h r s

/-- Descending recovery of all bar-invariant multiplicities from a proposed
correction. The residual hypotheses are coefficient identities to be proved
in an application; neither the desired multiplicities nor row sum is assumed.

For the manuscript, `a` is the full-spherical canonical multiplicity,
`g r = correction (m-r)`, and strict positivity of the two residuals comes
respectively from the other canonical families and Gaussian cancellation. -/
theorem descending_correction (n : ℕ) (h : ℕ → ℕ → LP)
    (a g raw : ℕ → LP)
    (ha : ∀ r < n, BarSymmetric (a r))
    (hg : ∀ r < n, BarSymmetric (g r))
    (hactual : ∀ r < n, LowerBound (raw r - triangularExpansion n h a r) 1)
    (hproposed : ∀ r < n, LowerBound (raw r - triangularExpansion n h g r) 1) :
    ∀ r < n, a r = g r := by
  have aux : ∀ k : ℕ, ∀ r < n, n - r ≤ k → a r = g r := by
    intro k
    induction k with
    | zero =>
        intro r hr hkr
        omega
    | succ k ih =>
        intro r hr hkr
        have hsum :
            (∑ s ∈ (Finset.range n).filter (r < ·), a s * h r s) =
            ∑ s ∈ (Finset.range n).filter (r < ·), g s * h r s := by
          apply Finset.sum_congr rfl
          intro s hs
          obtain ⟨hsn, hrs⟩ := Finset.mem_filter.mp hs
          have hsn' := Finset.mem_range.mp hsn
          rw [ih s hsn' (by omega)]
        apply eq_of_positive_difference (ha r hr) (hg r hr)
        have hdiff := lowerBound_sub (hproposed r hr) (hactual r hr)
        have heq :
            (raw r - triangularExpansion n h g r) -
              (raw r - triangularExpansion n h a r) = a r - g r := by
          unfold triangularExpansion
          rw [hsum]
          abel
        rwa [heq] at hdiff
  intro r hr
  exact aux (n - r) r hr le_rfl

/-- After the full-spherical terms have been removed, contributions starting
in degree three cannot alter the critical coefficient. This reads actual
Laurent coordinates, without defining `mu` to be the desired row sum. -/
theorem critical_readout {ι κ : Type*} (desired : Finset ι) (other : Finset κ)
    (coeff : ι → LP) (remainder : κ → LP) (corrected : LP)
    (hexpansion : corrected = (∑ j ∈ desired, coeff j) + ∑ s ∈ other, remainder s)
    (hmargin : ∀ s ∈ other, LowerBound (remainder s) 3) :
    corrected 1 = ∑ j ∈ desired, coeff j 1 := by
  have hz : (∑ s ∈ other, remainder s) 1 = 0 :=
    lowerBound_sum other remainder hmargin 1 (by omega)
  rw [hexpansion, coeff_add, hz, add_zero]
  change coeffHom 1 (∑ j ∈ desired, coeff j) = _
  rw [map_sum]
  rfl

end Guralnick.CanonicalCorrection
