import Guralnick.Positivity
import Mathlib.Tactic

/-!
# The concrete one-line degree and multiplicity-one margins

These are the polynomial identities and integer inequalities in Sections 5
and 7. The two degree excesses are computed from the displayed Gaussian
piece degrees and the displayed length deficit, rather than assumed as
inequalities. Feasibility retains the nonempty-piece branches.

The correspondence of the count with the actual web's standard coefficients
remains a separate gallery-counting statement; this file does not identify
an arbitrary polynomial with a canonical coefficient by definition.
-/

namespace Guralnick.CanonicalOneLine

open Positivity

def codimension (n d a b : ℤ) : ℤ :=
  b * (d + b) + a * (n - d + a - b)

def lengthGap (n s d a b : ℤ) : ℤ :=
  2 * s * (n - s) - (n - d - s + 1) + codimension n d a b

def firstDegree (n s a : ℤ) : ℤ := a - 1 + s * (n - s)
def secondDegree (n s c : ℤ) : ℤ := c - 1 + (s - 1) * (n - s)

/-- Exact subtraction for the first nonempty Gaussian piece. -/
theorem first_excess (n s d a b : ℤ) :
    2 * firstDegree n s a - lengthGap n s d a b =
      -(a - 1) * (n - d + a - 1) + b * (a - d - b) - s := by
  unfold firstDegree lengthGap codimension
  ring

/-- Exact subtraction for the second nonempty Gaussian piece, with `c=d+b`. -/
theorem second_excess (n s d a b : ℤ) :
    2 * secondDegree n s (d + b) - lengthGap n s d a b =
      -(n - d) + s - 1 + b * (2 - d - b) - a * (n - d + a - b) := by
  unfold secondDegree lengthGap codimension
  ring

/-- Every first piece has nonpositive excess, using the actual finite-flag
feasibility inequalities. `a>=1` is essential: this is the nonempty branch. -/
theorem first_nonpositive (n s d a b : ℤ)
    (hs : 0 ≤ s) (hnd : s ≤ n - d) (ha : 1 ≤ a)
    (hb : 0 ≤ b) (hab : a ≤ d + b) :
    2 * firstDegree n s a - lengthGap n s d a b ≤ 0 := by
  rw [first_excess]
  have hp : 0 ≤ (a - 1) * (n - d + a - 1) :=
    mul_nonneg (by omega) (by omega)
  have hq : b * (a - d - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (by omega)
  nlinarith

/-- Equality in the first-piece bound gives the unique leading standard:
`s=0,a=1,b=0` for `d>=1`, and `s=0,a=b=1` for `d=0`. -/
theorem first_equality_positions (n s d a b : ℤ)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hnd : s ≤ n - d)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (hab : a ≤ d + b)
    (he : 2 * firstDegree n s a - lengthGap n s d a b = 0) :
    s = 0 ∧ a = 1 ∧ ((1 ≤ d ∧ b = 0) ∨ (d = 0 ∧ b = 1)) := by
  rw [first_excess] at he
  have hp : 0 ≤ (a - 1) * (n - d + a - 1) :=
    mul_nonneg (by omega) (by omega)
  have hq : b * (a - d - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (by omega)
  have hs0 : s = 0 := by nlinarith
  have hp0 : (a - 1) * (n - d + a - 1) = 0 := by nlinarith
  have ha1 : a = 1 := by
    rcases mul_eq_zero.mp hp0 with h | h <;> omega
  refine ⟨hs0, ha1, ?_⟩
  subst s
  subst a
  by_cases hd0 : d = 0
  · right
    refine ⟨hd0, ?_⟩
    subst d
    have hbb : b * (1 - b) = 0 := by nlinarith
    rcases mul_eq_zero.mp hbb with h | h <;> omega
  · left
    refine ⟨by omega, ?_⟩
    have hbb : b * (1 - d - b) = 0 := by nlinarith
    rcases mul_eq_zero.mp hbb with h | h <;> omega

/-- The second nonempty Gaussian piece is strictly below the leading
standard. This includes the `d=0` endpoint without applying a negative
Gaussian index degree formula. -/
theorem second_negative (n s d a b : ℤ)
    (hn : 1 ≤ n) (hs : 0 ≤ s) (hsd : s ≤ d) (hnd : s ≤ n - d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ n - d + a) :
    2 * secondDegree n s (d + b) - lengthGap n s d a b < 0 := by
  rw [second_excess]
  have hp : 0 ≤ a * (n - d + a - b) := mul_nonneg ha (by omega)
  by_cases hd : d = 0
  · have hs0 : s = 0 := by omega
    subst d
    subst s
    have hbb : b * (2 - b) ≤ 1 := by nlinarith [sq_nonneg (b - 1)]
    nlinarith
  · have hd1 : 1 ≤ d := by omega
    have hbb : b * (2 - d - b) ≤ 0 := by
      by_cases hb0 : b = 0
      · simp [hb0]
      · have hb1 : 1 ≤ b := by omega
        exact mul_nonpos_of_nonneg_of_nonpos hb (by omega)
    omega

/-- Positive powers of `v` for every nonleading first piece, expressed
integrally rather than as a real-valued degree inequality. -/
theorem first_strict_off_leading (n s d a b : ℤ)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hnd : s ≤ n - d)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (hab : a ≤ d + b)
    (hne : ¬ (s = 0 ∧ a = 1 ∧ ((1 ≤ d ∧ b = 0) ∨ (d = 0 ∧ b = 1)))) :
    1 ≤ lengthGap n s d a b - 2 * firstDegree n s a := by
  have hle := first_nonpositive n s d a b hs hnd ha hb hab
  have hne' : 2 * firstDegree n s a - lengthGap n s d a b ≠ 0 := by
    intro he
    exact hne (first_equality_positions n s d a b hs hd hnd ha hb hab he)
  omega

/-! ## Section 7: margins at the desired family standards -/

/-- The full-spherical refinement contribution has margin `2h+6`. -/
theorem spherical_margin (k h : ℤ) :
    (2 * k + 3) - (2 * (k - h) - 3) = 2 * h + 6 := by ring

/-- At the target family matrix, the two-row codimension is `2k+2`
for the strong (`f=m`) output. The refinement adds one further power. -/
theorem strong_codimension (k : ℤ) :
    codimension (2 * k + 1) k 1 1 = 2 * k + 2 := by
  unfold codimension
  ring

theorem weak_codimension (k : ℤ) :
    codimension (2 * k + 1) (k + 1) 1 1 = 2 * k + 2 := by
  unfold codimension
  ring

/-- Degree difference between the two polynomial pieces at the desired
standard in the strong case. For `h=0` the second piece is absent. -/
theorem strong_piece_degree_difference (k h : ℤ) :
    h * (2 * k + 1 - h) - (k + (h - 1) * (2 * k + 1 - h)) =
      (k - h) + 1 := by ring

theorem weak_piece_degree_difference (k h : ℤ) :
    h * (2 * k + 1 - h) - (k + 1 + (h - 1) * (2 * k + 1 - h)) =
      k - h := by ring

theorem strong_refined_minimum (k h : ℤ) :
    lengthGap (2 * k + 1) h k 1 1 + 1 -
      2 * (h * (2 * k + 1 - h)) = (k - h) + 2 * h + 1 := by
  unfold lengthGap codimension
  ring

theorem weak_refined_minimum (k h : ℤ) :
    lengthGap (2 * k + 1) h (k + 1) 1 1 + 1 -
      2 * (h * (2 * k + 1 - h)) = (k - h) + 2 * h + 2 := by
  unfold lengthGap codimension
  ring

/-- Genuine Laurent-polynomial multiplication now converts the computed
strong margin and the multiplicity bound into exclusion of the constant
term. No coefficientwise positivity of the multiplicity is required. -/
theorem strong_contribution_margin {p q : LP} (k h : ℤ)
    (hp : LowerBound p (-(k - h - 1)))
    (hq : LowerBound q ((k - h) + 2 * h + 1)) :
    LowerBound (p * q) (2 * h + 2) := by
  have he : -(k - h - 1) + ((k - h) + 2 * h + 1) = 2 * h + 2 := by ring
  simpa only [he] using lowerBound_mul hp hq

theorem weak_contribution_margin {p q : LP} (k h : ℤ)
    (hp : LowerBound p (-(k - h - 2)))
    (hq : LowerBound q ((k - h) + 2 * h + 2)) :
    LowerBound (p * q) (2 * h + 4) := by
  have he : -(k - h - 2) + ((k - h) + 2 * h + 2) = 2 * h + 4 := by ring
  simpa only [he] using lowerBound_mul hp hq

theorem spherical_contribution_margin {p q : LP} (k h : ℤ)
    (hp : LowerBound p (-(2 * (k - h) - 3)))
    (hq : LowerBound q (2 * k + 3)) : LowerBound (p * q) (2 * h + 6) := by
  have he : -(2 * (k - h) - 3) + (2 * k + 3) = 2 * h + 6 := by ring
  simpa only [he] using lowerBound_mul hp hq

end Guralnick.CanonicalOneLine
