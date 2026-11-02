import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Guralnick.Affine

/-!
# Uniform integer-coordinate checks for the highest weights

This file constructs the actual coordinate vector displayed in Section 10.
It proves uniform root-lattice, dominance, restrictedness and p-regularity
statements.
It does not construct a highest-weight representation or prove Andersen's
cohomological theorem. Identification with the inverse sorted affine window
is a separate bridge to `Guralnick/Affine.lean`.
-/

namespace Guralnick.Weights

open scoped BigOperators

/-- The first `m` coordinates, using zero-based coordinate indices. -/
def leftCoordinate (m j p i : ℕ) : ℤ :=
  if i + 1 < j then p
  else if i + 1 = j then (p : ℤ) - m + j - 2
  else 1

/-- The manuscript's vector
`(p^(j-1), p-(m-j)-2, 1^(m-j), 0,
  (-1)^(m-j), (m-j)+2-p, (-p)^(j-1))`.
The superscripts in this display mean repetition, not powers. -/
def coordinate (m j p : ℕ) (i : Fin (2 * m + 1)) : ℤ :=
  if i.val < m then leftCoordinate m j p i.val
  else if i.val = m then 0
  else -leftCoordinate m j p (2 * m - i.val)

/-- Integral sum-zero coordinates are the standard type-A root-lattice model. -/
def RootLattice (n : ℕ) := { x : Fin n → ℤ // ∑ i, x i = 0 }

theorem coordinate_rev (m j p : ℕ) (i : Fin (2 * m + 1)) :
    coordinate m j p i.rev = -coordinate m j p i := by
  have hi := i.isLt
  simp only [coordinate, Fin.val_rev, Nat.add_sub_add_right]
  by_cases h : i.val < m
  · have h₁ : ¬(2 * m - i.val < m) := by omega
    have h₂ : ¬(2 * m - i.val = m) := by omega
    have h₃ : 2 * m - (2 * m - i.val) = i.val := by omega
    simp [h, h₁, h₂, h₃]
  · by_cases heq : i.val = m
    · have hrev : 2 * m - m = m := by omega
      simp [heq, hrev]
    · have hrev : 2 * m - i.val < m := by omega
      simp [h, heq, hrev]

theorem sum_coordinates (m j p : ℕ) : ∑ i, coordinate m j p i = 0 := by
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))
    (coordinate m j p)
  simp only [Fin.revPerm_apply, coordinate_rev, Finset.sum_neg_distrib] at h
  omega

/-- The family is genuinely an element of the integral sum-zero lattice. -/
def familyWeight (m j p : ℕ) : RootLattice (2 * m + 1) :=
  ⟨coordinate m j p, sum_coordinates m j p⟩

/-- Dynkin labels are adjacent coordinate differences, rather than separately
postulated target coefficients. -/
def dynkin (m j p : ℕ) (i : Fin (2 * m)) : ℤ :=
  coordinate m j p i.castSucc - coordinate m j p i.succ

theorem leftCoordinate_positive {m j p i : ℕ}
    (hm : 2 ≤ m) (_hj : 1 ≤ j) (hjm : j ≤ m) (hp : 2 * m + 1 < p) :
    0 < leftCoordinate m j p i := by
  unfold leftCoordinate
  split_ifs <;> omega

/-- Every adjacent difference is a valid p-restricted dominant Dynkin label. -/
theorem dynkin_bounds {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (hp : 2 * m + 1 < p)
    (i : Fin (2 * m)) :
    0 ≤ dynkin m j p i ∧ dynkin m j p i < (p : ℤ) := by
  have hi := i.isLt
  simp only [dynkin, coordinate, Fin.coe_castSucc, Fin.val_succ]
  unfold leftCoordinate
  split_ifs <;> omega

theorem familyWeight_nonzero {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (hp : 2 * m + 1 < p) :
    coordinate m j p ≠ 0 := by
  intro h
  have hzero := congrFun h (⟨0, by omega⟩ : Fin (2 * m + 1))
  have hpos := leftCoordinate_positive (i := 0) hm hj hjm hp
  have hmpos : 0 < m := by omega
  simp [coordinate, hmpos] at hzero
  omega

/-- Coordinates of the half-sum of positive roots in type `A_(2m)`. -/
def rho (m : ℕ) (i : Fin (2 * m + 1)) : ℤ := (m : ℤ) - i.val

/-- Small representatives for the first half of `lambda + rho` modulo `p`. -/
def leftResidue (m j i : ℕ) : ℤ :=
  if i + 1 < j then (m : ℤ) - i
  else if i + 1 = j then -1
  else (m : ℤ) + 1 - i

/-- These small representatives permute the integers from `-m` to `m`. -/
def smallResidue (m j : ℕ) (i : Fin (2 * m + 1)) : ℤ :=
  if i.val < m then leftResidue m j i.val
  else if i.val = m then 0
  else -leftResidue m j (2 * m - i.val)

theorem smallResidue_bounds {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (i : Fin (2 * m + 1)) :
    -(m : ℤ) ≤ smallResidue m j i ∧ smallResidue m j i ≤ (m : ℤ) := by
  have hi := i.isLt
  unfold smallResidue leftResidue
  split_ifs <;> omega

theorem smallResidue_injective {m j : ℕ} (_hm : 2 ≤ m) (_hj : 1 ≤ j)
    (hjm : j ≤ m) : Function.Injective (smallResidue m j) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  unfold smallResidue leftResidue at hab
  split_ifs at hab <;> omega

theorem shifted_modEq_smallResidue {m j p : ℕ} (i : Fin (2 * m + 1)) :
    coordinate m j p i + rho m i ≡ smallResidue m j i [ZMOD (p : ℤ)] := by
  have hi := i.isLt
  apply Int.modEq_iff_dvd.mpr
  unfold coordinate rho smallResidue leftCoordinate leftResidue
  split_ifs <;>
    first
    | exact ⟨0, by omega⟩
    | exact ⟨1, by omega⟩
    | exact ⟨-1, by omega⟩

/-- The actual coordinate criterion for p-regularity: no two coordinates of
`lambda + rho` are congruent modulo `p`. This is not a representation-theoretic
regularity predicate introduced as an assumption. -/
def PRegular (m p : ℕ) (x : Fin (2 * m + 1) → ℤ) : Prop :=
  Function.Injective (fun i => (x i + rho m i) % (p : ℤ))

theorem familyWeight_pRegular {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (hp : 2 * m + 1 < p) :
    PRegular m p (coordinate m j p) := by
  intro a b hab
  have ha := smallResidue_bounds hm hj hjm a
  have hb := smallResidue_bounds hm hj hjm b
  have hab' : smallResidue m j a ≡ smallResidue m j b [ZMOD (p : ℤ)] :=
    (shifted_modEq_smallResidue a).symm.trans
      ((show coordinate m j p a + rho m a ≡ coordinate m j p b + rho m b
          [ZMOD (p : ℤ)] from hab).trans (shifted_modEq_smallResidue b))
  apply smallResidue_injective hm hj hjm
  by_cases hle : smallResidue m j a ≤ smallResidue m j b
  · have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega)
      (show smallResidue m j b - smallResidue m j a < (p : ℤ) by omega)
      hab'.dvd
    omega
  · have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega)
      (show smallResidue m j a - smallResidue m j b < (p : ℤ) by omega)
      hab'.symm.dvd
    omega

/-- Compatibility with the coordinate predicate used by the affine-window
certificates. This theorem is uniform, not a finite certificate check. -/
theorem familyWeight_dominantRestricted {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (hp : 2 * m + 1 < p) :
    Guralnick.DominantRestricted (p : ℤ) (coordinate m j p) := by
  intro a b hab
  have hb := b.isLt
  have ha : a.val < 2 * m := by omega
  let i : Fin (2 * m) := ⟨a.val, ha⟩
  have hia : i.castSucc = a := Fin.ext rfl
  have hib : i.succ = b := Fin.ext hab
  simpa only [dynkin, hia, hib] using dynkin_bounds hm hj hjm hp i

/-- The equivalent affine-root coordinate test from `Affine.lean`. -/
theorem familyWeight_regular {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (hp : 2 * m + 1 < p) :
    Guralnick.Regular (p : ℤ) (rho m) (coordinate m j p) := by
  intro a b hne hzero
  apply hne
  apply familyWeight_pRegular hm hj hjm hp
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  simpa only [sub_add_eq_sub_sub] using hzero

end Guralnick.Weights
