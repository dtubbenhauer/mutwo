import Guralnick.CanonicalApplication

/-!
# The six canonical multiplicity bounds

This is the allowance table of Proposition algebraic-six, applied to
actual canonical coefficients of the six-map Hecke element. Each bound
comes from a proved degree estimate and cleared-denominator positivity.
The count-to-coordinate link remains a separate theorem.
-/

noncomputable section
namespace Guralnick.CanonicalMultiplicityBounds
open Hecke ParabolicWeb Positivity CanonicalGallery

inductive Pattern where
  | full | weakDual | strongDual | weak | strong | two
  deriving DecidableEq

def a : Pattern → ℤ
  | .strong | .two => 1
  | _ => 0

def s : Pattern → ℤ
  | .weakDual | .strongDual | .two => 1
  | _ => 0

def beta : Pattern → ℤ
  | .weak => 1
  | _ => 0

def delta : Pattern → ℤ
  | .weakDual => 0
  | _ => 1

def increment : Pattern → ℤ
  | .full => 0
  | .weakDual | .weak => 1
  | .strongDual | .strong => 2
  | .two => 3

def allowance (p : Pattern) (l : ℤ) : ℤ :=
  match p with
  | .full => 2*l-3
  | .weakDual | .weak => l-2
  | .strongDual | .strong => l-1
  | .two => 0

def Matches {m : ℕ} (A : CanonicalMatrix.PacketMatrix m) (p : Pattern) : Prop :=
  A.a=a p ∧ A.s=s p ∧ A.beta=beta p ∧ A.delta=delta p

theorem pattern_of_six {m : ℕ} (A : CanonicalMatrix.PacketMatrix m)
    (h : DegreeBounds.SixPositions A.beta A.delta A.a A.s) :
    ∃ p : Pattern, Matches A p := by
  rcases h with ⟨hb,hd,ha,hs⟩ | ⟨hb,hd,ha,hs⟩ | ⟨hb,hd,ha,hs⟩
  · rcases ha with ha|ha <;> rcases hs with hs|hs
    · exact ⟨.full, ha, hs, hb, hd⟩
    · exact ⟨.strongDual, ha, hs, hb, hd⟩
    · exact ⟨.strong, ha, hs, hb, hd⟩
    · exact ⟨.two, ha, hs, hb, hd⟩
  · exact ⟨.weakDual, ha, hs, hb, hd⟩
  · exact ⟨.weak, ha, hs, hb, hd⟩

theorem degree_bound (p : Pattern) (l : ℤ) (hl : 1≤l) :
    CoeffBound (count l (a p) (s p) (beta p) (delta p))
      (baseDegree l+increment p) := by
  cases p with
  | full =>
    simpa [a, s, beta, delta, increment, degreeBound01] using
      count_bound01 l 0 0 (by omega) (by omega) (by omega) (by omega)
  | weakDual =>
    simpa [a, s, beta, delta, increment, degreeBound00] using
      count_bound00 l 0 1 (by omega) (by omega)
  | strongDual =>
    simpa [a, s, beta, delta, increment, degreeBound01] using
      count_bound01 l 0 1 (by omega) (by omega) (by omega) (by omega)
  | weak =>
    simpa [a, s, beta, delta, increment, degreeBound11] using
      count_bound11 l 0 0 (by omega) (by omega)
  | strong =>
    simpa [a, s, beta, delta, increment, degreeBound01] using
      count_bound01 l 1 0 (by omega) (by omega) (by omega) (by omega)
  | two =>
    simpa [a, s, beta, delta, increment, degreeBound01, add_assoc] using
      count_bound01 l 1 1 (by omega) (by omega) (by omega) (by omega)

theorem allowance_identity (p : Pattern) (l : ℤ) :
    gap l (a p) (s p) (beta p) (delta p)-2*(baseDegree l+increment p) =
      -allowance p l := by
  cases p <;> simp only [a, s, beta, delta, increment, allowance,
    gap, codimension, baseDegree] <;> ring

theorem count_lowerBound (p : Pattern) (l : ℤ) (hl : 1≤l) :
    LowerBound (normalize (gap l (a p) (s p) (beta p) (delta p))
      (count l (a p) (s p) (beta p) (delta p))) (-allowance p l) := by
  have h := normalized_lowerBound (gap l (a p) (s p) (beta p) (delta p))
    _ _ (degree_bound p l hl)
  rwa [allowance_identity] at h

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D) (P : PositivityInput K)

include P

/-- Bounds on actual raw standard coordinates pass to canonical multiplicities. -/
theorem raw_multiplicity_bounds (w : AffinePermutation (2*m+1)) (b : ℤ)
    (hstd : LowerBound (K.standard.repr (Family.raw K D L) w) b) :
    LowerBound (K.canonical.repr (Family.raw K D L) w) b ∧
      UpperBound (K.canonical.repr (Family.raw K D L) w) (-b) := by
  obtain ⟨rest, hrest, heq⟩ := positive_cleared_coordinate_identity K P
    (scalar D (Family.output m)*scalar D (Family.common m)^2)
    (Family.raw K D L) (Family.raw_cleared_nonnegative K D L P) w
  exact cleared_support_bounds (Family.denominator_ne_zero K D L)
    (Family.raw_cleared_nonnegative K D L P w) hrest heq hstd
    (Family.raw_canonical_bar K D L w)

/-- The actual multiplicity is supported in the precise interval [-E,E]. -/
theorem pattern_multiplicity_bounds (w : AffinePermutation (2*m+1))
    (p : Pattern) (l : ℤ) (hl : 1≤l)
    (hcount : K.standard.repr (Family.raw K D L) w =
      normalize (gap l (a p) (s p) (beta p) (delta p))
        (count l (a p) (s p) (beta p) (delta p))) :
    LowerBound (K.canonical.repr (Family.raw K D L) w) (-allowance p l) ∧
      UpperBound (K.canonical.repr (Family.raw K D L) w) (allowance p l) := by
  have hs : LowerBound (K.standard.repr (Family.raw K D L) w) (-allowance p l) := by
    rw [hcount]
    exact count_lowerBound p l hl
  simpa only [neg_neg] using raw_multiplicity_bounds K D L P w _ hs

/-- A table entry with negative allowance contributes no canonical term. -/
theorem pattern_vanishes (w : AffinePermutation (2*m+1))
    (p : Pattern) (l : ℤ) (hl : 1≤l) (hneg : allowance p l<0)
    (hcount : K.standard.repr (Family.raw K D L) w =
      normalize (gap l (a p) (s p) (beta p) (delta p))
        (count l (a p) (s p) (beta p) (delta p))) :
    K.canonical.repr (Family.raw K D L) w=0 :=
  eq_zero_of_positive_bar_bound (Family.raw_canonical_bar K D L w)
    (pattern_multiplicity_bounds K D L P w p l hl hcount).1 (by omega)

end Guralnick.CanonicalMultiplicityBounds
