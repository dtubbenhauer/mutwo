import Mathlib.Tactic

/-!
# Uniform arithmetic in the six-family exclusion

These theorems formalize the integer polynomial inequalities in Section 4
of `PolishedWebProof/main.tex`, lines 4460–4506. They are universal in the
parameters, not finite computation checks.

Scope: the hypotheses explicitly include the proposed upper bound on an
integer `E`. This file does not prove that this bound is the degree of a
Gaussian count, that `E` controls canonical multiplicities, or that any
matrix labels a KL coefficient. Those are separate mathematical bridges.
-/

namespace Guralnick.DegreeBounds

/-- The symmetric bound for the middle-row case `(β,δ)=(0,1)`, with
`M=max(a,s)` and `u=min(a,s)`. The diagonal receives the extra two. -/
def symmetricBound (l M u : ℤ) : ℤ :=
  (2 - M - u) * l - M^2 - u^2 + M*u + 3*M - u - 3 +
    if M = u ∧ 1 ≤ u then 2 else 0

theorem symmetricBound_negative (l M u : ℤ)
    (hl : 1 ≤ l) (hM : 2 ≤ M) (hu : 0 ≤ u) (horder : u ≤ M) :
    symmetricBound l M u < 0 := by
  unfold symmetricBound
  by_cases hdiag : M = u
  · subst u
    rw [if_pos (show M = M ∧ 1 ≤ M from ⟨rfl, by omega⟩)]
    have hp : 0 ≤ (M - 1) * (l - 1) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (M - 1)]
  · simp only [hdiag, false_and, if_false, add_zero]
    by_cases hu0 : u = 0
    · subst u
      have hp : 0 ≤ (M - 2) * (l - 1) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg (M - 1)]
    · by_cases hu1 : u = 1
      · subst u
        have hp : 0 ≤ (M - 1) * (l - 1) := mul_nonneg (by omega) (by omega)
        nlinarith [sq_nonneg (M - 2)]
      · have hu2 : 2 ≤ u := by omega
        have hp : 0 ≤ (M + u - 2) * (l - 1) :=
          mul_nonneg (by omega) (by omega)
        have hq : 0 ≤ (u - 2) * (M - u) :=
          mul_nonneg (by omega) (by omega)
        nlinarith [sq_nonneg u, sq_nonneg (M - u)]

/-- Case `(β,δ)=(0,1)`: only the four positions A, C, E, F remain. -/
theorem case01_positions (l a s E : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (hs : 0 ≤ s) (hE : 0 ≤ E)
    (hbound : E ≤ symmetricBound l (max a s) (min a s)) :
    (a = 0 ∨ a = 1) ∧ (s = 0 ∨ s = 1) := by
  have hmax : max a s ≤ 1 := by
    by_contra h
    have hm : 2 ≤ max a s := by omega
    have hu : 0 ≤ min a s := le_min ha hs
    have horder : min a s ≤ max a s := (min_le_left a s).trans (le_max_left a s)
    have hn := symmetricBound_negative l (max a s) (min a s) hl hm hu horder
    omega
  have haa := (le_max_left a s).trans hmax
  have hss := (le_max_right a s).trans hmax
  omega

def bound00High (l a s : ℤ) : ℤ :=
  (2-a-s)*l - a^2 - s^2 + a*s + 3*a - 3

def bound00Low (l a s : ℤ) : ℤ :=
  (2-a-s)*l - a^2 - s^2 + a*s + 4*s - a - 5

theorem bound00High_negative (l a s : ℤ)
    (hl : 1 ≤ l) (hs : 1 ≤ s) (horder : s ≤ a) :
    bound00High l a s < 0 := by
  unfold bound00High
  by_cases hs1 : s = 1
  · subst s
    by_cases ha1 : a = 1
    · subst a
      norm_num
    · have ha2 : 2 ≤ a := by omega
      have hp : 0 ≤ (a - 1) * (l - 1) := mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg (a - 2)]
  · have hs2 : 2 ≤ s := by omega
    have hp : 0 ≤ (a + s - 2) * (l - 1) := mul_nonneg (by omega) (by omega)
    have hq : 0 ≤ (s - 2) * (a - s) := mul_nonneg (by omega) (by omega)
    have hr : 0 ≤ s * (s - 1) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (a - s)]

theorem bound00Low_negative (l a s : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (hs : 2 ≤ s) (horder : a + 1 ≤ s) :
    bound00Low l a s < 0 := by
  unfold bound00Low
  by_cases ha0 : a = 0
  · subst a
    have hp : 0 ≤ (s - 2) * (l - 1) := mul_nonneg (by omega) (by omega)
    have hq : 0 ≤ (s - 2) * (s - 1) := mul_nonneg (by omega) (by omega)
    nlinarith
  · have ha1 : 1 ≤ a := by omega
    have hp : 0 ≤ (a + s - 2) * (l - 1) := mul_nonneg (by omega) (by omega)
    have hq : 0 ≤ (a - 1) * (s - a - 1) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg a, sq_nonneg (s - a - 1)]

/-- Case `(β,δ)=(0,0)`: only position B, `a=0,s=1`, remains. -/
theorem case00_position (l a s E : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (hs : 1 ≤ s) (hE : 0 ≤ E)
    (hbound : E ≤ if s ≤ a then bound00High l a s else bound00Low l a s) :
    a = 0 ∧ s = 1 := by
  by_cases horder : s ≤ a
  · rw [if_pos horder] at hbound
    have hn := bound00High_negative l a s hl hs horder
    omega
  · rw [if_neg horder] at hbound
    have horder' : a + 1 ≤ s := by omega
    by_cases hs1 : s = 1
    · omega
    · have hs2 : 2 ≤ s := by omega
      have hn := bound00Low_negative l a s hl ha hs2 horder'
      omega

def bound11High (l a s : ℤ) : ℤ :=
  (1-a-s)*l - a^2 - s^2 + a*s + 2*a - 2

def bound11Low (l a s : ℤ) : ℤ :=
  (1-a-s)*l - a^2 - s^2 + a*s - 2*a + 4*s - 4

theorem bound11High_negative (l a s : ℤ)
    (hl : 1 ≤ l) (ha : 1 ≤ a) (hs : 0 ≤ s) (horder : s ≤ a) :
    bound11High l a s < 0 := by
  unfold bound11High
  have hp : 0 ≤ (a + s - 1) * (l - 1) := mul_nonneg (by omega) (by omega)
  by_cases hs0 : s = 0
  · subst s
    have hq : 0 ≤ a * (a - 1) := mul_nonneg (by omega) (by omega)
    nlinarith
  · have hs1 : 1 ≤ s := by omega
    have hq : 0 ≤ (s - 1) * (a - s) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg s, sq_nonneg (a - s)]

theorem bound11Low_negative (l a s : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (horder : a + 1 ≤ s) :
    bound11Low l a s < 0 := by
  unfold bound11Low
  have hp : 0 ≤ (a + s - 1) * (l - 1) := mul_nonneg (by omega) (by omega)
  by_cases ha0 : a = 0
  · subst a
    by_cases hs1 : s = 1
    · subst s
      norm_num
    · have hs2 : 2 ≤ s := by omega
      have hq : 0 ≤ (s - 1) * (s - 2) := mul_nonneg (by omega) (by omega)
      nlinarith
  · have ha1 : 1 ≤ a := by omega
    have hq : 0 ≤ (a - 1) * (s - a) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg a, sq_nonneg (s - a - 1)]

/-- Case `(β,δ)=(1,1)`: only position D, `a=s=0`, remains. -/
theorem case11_position (l a s E : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (hs : 0 ≤ s) (hE : 0 ≤ E)
    (hbound : E ≤ if s ≤ a then bound11High l a s else bound11Low l a s) :
    a = 0 ∧ s = 0 := by
  by_cases horder : s ≤ a
  · rw [if_pos horder] at hbound
    by_cases ha0 : a = 0
    · omega
    · have ha1 : 1 ≤ a := by omega
      have hn := bound11High_negative l a s hl ha1 hs horder
      omega
  · rw [if_neg horder] at hbound
    have horder' : a + 1 ≤ s := by omega
    have hn := bound11Low_negative l a s hl ha horder'
    omega

/-- The three middle rows of a feasible matrix in the manuscript. -/
def MiddleRow (β δ : ℤ) : Prop :=
  (β = 0 ∧ δ = 1) ∨ (β = 0 ∧ δ = 0) ∨ (β = 1 ∧ δ = 1)

/-- The six parameter positions; the first disjunct comprises A, C, E, F,
and the last two are B and D. This definition is purely arithmetic. -/
def SixPositions (β δ a s : ℤ) : Prop :=
  (β = 0 ∧ δ = 1 ∧ (a = 0 ∨ a = 1) ∧ (s = 0 ∨ s = 1)) ∨
  (β = 0 ∧ δ = 0 ∧ a = 0 ∧ s = 1) ∨
  (β = 1 ∧ δ = 1 ∧ a = 0 ∧ s = 0)

/-- Combined uniform arithmetic exclusion. The degree-bound implications
are hypotheses, not assertions about Gaussian or canonical coefficients. -/
theorem six_positions_of_bounds (l a s E β δ : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (hs : 0 ≤ s) (hE : 0 ≤ E)
    (hrow : MiddleRow β δ) (hfeas : δ = 0 → 1 ≤ s)
    (h01 : β = 0 → δ = 1 → E ≤ symmetricBound l (max a s) (min a s))
    (h00 : β = 0 → δ = 0 →
      E ≤ if s ≤ a then bound00High l a s else bound00Low l a s)
    (h11 : β = 1 → δ = 1 →
      E ≤ if s ≤ a then bound11High l a s else bound11Low l a s) :
    SixPositions β δ a s := by
  rcases hrow with ⟨hb, hd⟩ | ⟨hb, hd⟩ | ⟨hb, hd⟩
  · have h := case01_positions l a s E hl ha hs hE (h01 hb hd)
    exact Or.inl ⟨hb, hd, h.1, h.2⟩
  · have h := case00_position l a s E hl ha (hfeas hd) hE (h00 hb hd)
    exact Or.inr (Or.inl ⟨hb, hd, h.1, h.2⟩)
  · have h := case11_position l a s E hl ha hs hE (h11 hb hd)
    exact Or.inr (Or.inr ⟨hb, hd, h.1, h.2⟩)

/-- The boundary row of the table, `l=0`, has only the type-F position.
The two alternatives in each off-central row are the table's cases
`s=a` and `s=a+1`; retaining the disjunction also handles feasibility. -/
theorem boundary_position_of_bounds (a s E β δ : ℤ)
    (ha : 1 ≤ a) (hE : 0 ≤ E) (hrow : MiddleRow β δ)
    (h01 : β = 0 → δ = 1 → s = a ∧ E ≤ -(a-1)^2)
    (h00 : β = 0 → δ = 0 →
      (s = a ∧ E ≤ -a^2 + 3*a - 3) ∨
      (s = a+1 ∧ E ≤ -(a-1)^2 - 1))
    (h11 : β = 1 → δ = 1 →
      (s = a ∧ E ≤ -(a-1)^2 - 1) ∨
      (s = a+1 ∧ E ≤ -a^2 + a - 1)) :
    β = 0 ∧ δ = 1 ∧ a = 1 ∧ s = 1 := by
  rcases hrow with ⟨hb, hd⟩ | ⟨hb, hd⟩ | ⟨hb, hd⟩
  · obtain ⟨hs, hbnd⟩ := h01 hb hd
    have ha1 : a = 1 := by nlinarith [sq_nonneg (a - 1)]
    exact ⟨hb, hd, ha1, by omega⟩
  · rcases h00 hb hd with ⟨_, hbnd⟩ | ⟨_, hbnd⟩
    · by_cases ha1 : a = 1
      · nlinarith
      · have ha2 : 2 ≤ a := by omega
        have hp : 0 ≤ (a-1)*(a-2) := mul_nonneg (by omega) (by omega)
        nlinarith
    · nlinarith [sq_nonneg (a - 1)]
  · rcases h11 hb hd with ⟨_, hbnd⟩ | ⟨_, hbnd⟩
    · nlinarith [sq_nonneg (a - 1)]
    · have hp : 0 ≤ a*(a-1) := mul_nonneg (by omega) (by omega)
      nlinarith

end Guralnick.DegreeBounds
