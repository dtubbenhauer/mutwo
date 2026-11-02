import Guralnick.Weights
import Mathlib.Data.List.FinRange

/-!
# A uniform affine permutation realizing the weight family

This file constructs a genuine periodic affine permutation from the explicit
small residues. It proves the uniform inverse-dot-action identity. The relation
with the independently defined sorted input list `Guralnick.familyWindow` is
recorded separately below, rather than built into the definition.
-/

namespace Guralnick.Family

open scoped BigOperators
open Weights

/-- The zero-based residue corresponding to the small rho coordinate. -/
def residue {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  ⟨((m : ℤ) - smallResidue m j i).toNat, by
    have h := smallResidue_bounds hm hj hjm i
    omega⟩

theorem residue_value {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2 * m + 1)) :
    ((residue hm hj hjm i).val : ℤ) = (m : ℤ) - smallResidue m j i := by
  have h := smallResidue_bounds hm hj hjm i
  simp only [residue]
  omega

theorem residue_injective {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) : Function.Injective (residue hm hj hjm) := by
  intro a b hab
  have hval := congrArg (fun i : Fin (2 * m + 1) => (i.val : ℤ)) hab
  change ((residue hm hj hjm a).val : ℤ) = ((residue hm hj hjm b).val : ℤ) at hval
  rw [residue_value, residue_value] at hval
  apply smallResidue_injective hm hj hjm
  omega

noncomputable def residuePerm {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) : Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.ofBijective (residue hm hj hjm)
    (residue_injective hm hj hjm).bijective_of_finite

/-- The first `j` sorted entries have winding -1; the final `j` have +1. -/
def winding (m j : ℕ) (i : Fin (2 * m + 1)) : ℤ :=
  if i.val < j then -1 else if 2 * m + 1 - j ≤ i.val then 1 else 0

theorem winding_rev {m j : ℕ} (hjm : j ≤ m) (i : Fin (2 * m + 1)) :
    winding m j i.rev = -winding m j i := by
  have hi := i.isLt
  simp only [winding, Fin.val_rev, Nat.add_sub_add_right]
  split_ifs <;> norm_num <;> omega

theorem winding_balanced {m j : ℕ} (hjm : j ≤ m) : ∑ i, winding m j i = 0 := by
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))
    (winding m j)
  simp only [Fin.revPerm_apply, winding_rev hjm, Finset.sum_neg_distrib] at h
  omega

/-- This is an actual affine permutation, with a bijective residue map and
zero total winding, constructed uniformly for the whole family. -/
noncomputable def affine {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) : AffinePermutation (2 * m + 1) where
  residue := residuePerm hm hj hjm
  winding := winding m j
  balanced := winding_balanced hjm

theorem rho_residue {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2 * m + 1)) :
    rho m ((affine hm hj hjm).residue i) = smallResidue m j i := by
  change (m : ℤ) - ((residue hm hj hjm i).val : ℤ) = _
  rw [residue_value]
  ring

theorem coordinate_decomposition {m j p : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2 * m + 1)) :
    coordinate m j p i + rho m i =
      smallResidue m j i - (p : ℤ) * winding m j i := by
  have hi := i.isLt
  unfold coordinate rho smallResidue leftCoordinate leftResidue winding
  split_ifs <;> simp only [mul_neg, mul_one, mul_zero, neg_neg] <;> omega

/-- Uniform realization of the manuscript's coordinate vector as the inverse
positive p-dot action on zero. No primality or large-p assumption is needed. -/
theorem inverse_dotZero_eq_coordinate {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (affine hm hj hjm).inverse.dotZero (p : ℤ) (rho m) = coordinate m j p := by
  funext i
  rw [AffinePermutation.inverse_dotZero, rho_residue]
  change -(p : ℤ) * winding m j i + smallResidue m j i - rho m i = _
  have h := coordinate_decomposition (p := p) hj hjm i
  rw [neg_mul]
  omega

theorem entry_formula {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2 * m + 1)) :
    (affine hm hj hjm).entry i = (m : ℤ) - smallResidue m j i + 1 +
      (2 * m + 1 : ℕ) * winding m j i := by
  change ((residue hm hj hjm i).val : ℤ) + 1 +
    (2 * m + 1 : ℕ) * winding m j i = _
  rw [residue_value]

set_option maxHeartbeats 800000 in
/-- The constructed window is strictly increasing in its actual integer entries. -/
theorem entry_strictMono {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    StrictMono (affine hm hj hjm).entry := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  have hab' : a.val < b.val := hab
  have hra := smallResidue_bounds hm hj hjm a
  have hrb := smallResidue_bounds hm hj hjm b
  rw [entry_formula, entry_formula]
  unfold winding
  split_ifs <;> simp only [mul_neg, mul_one, mul_zero]
  all_goals try omega
  all_goals
    unfold smallResidue leftResidue
    split_ifs <;> omega

theorem winding_eq_inputShift {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (i : Fin (2 * m + 1)) :
    winding m j i = familyShift m j ((residue hm hj hjm i).val + 1) := by
  have hi := i.isLt
  have hz := (residue hm hj hjm i).isLt
  have hval := residue_value hm hj hjm i
  unfold winding familyShift
  split_ifs <;> unfold smallResidue leftResidue at hval <;>
    split_ifs at hval <;> omega

/-- The input entries before sorting, independently using the manuscript's
one-based shift function. -/
def originalEntry (m j : ℕ) (i : Fin (2 * m + 1)) : ℤ :=
  (i.val : ℤ) + 1 + (2 * m + 1 : ℕ) * familyShift m j (i.val + 1)

theorem entry_eq_original {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (i : Fin (2 * m + 1)) :
    (affine hm hj hjm).entry i = originalEntry m j ((affine hm hj hjm).residue i) := by
  change ((residue hm hj hjm i).val : ℤ) + 1 +
      (2 * m + 1 : ℕ) * winding m j i =
    ((residue hm hj hjm i).val : ℤ) + 1 +
      (2 * m + 1 : ℕ) * familyShift m j ((residue hm hj hjm i).val + 1)
  rw [winding_eq_inputShift]

theorem window_perm_original {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) :
    (affine hm hj hjm).window.Perm (List.ofFn (originalEntry m j)) := by
  have heq : (affine hm hj hjm).entry =
      originalEntry m j ∘ (affine hm hj hjm).residue :=
    funext (entry_eq_original hm hj hjm)
  rw [AffinePermutation.window, heq]
  exact (affine hm hj hjm).residue.ofFn_comp_perm (originalEntry m j)

theorem originalList_eq (m j : ℕ) :
    List.ofFn (originalEntry m j) =
      (List.range (2 * m + 1)).map (fun a =>
        ((a + 1 : ℕ) : ℤ) + (2 * m + 1 : ℕ) * familyShift m j (a + 1)) := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange (2 * m + 1), List.map_map]
  congr 1

/-- The actual affine permutation constructed here has exactly the independently
specified, sorted family window. This completes the uniform family bridge. -/
theorem window_eq_familyWindow {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) : (affine hm hj hjm).window = familyWindow m j := by
  unfold familyWindow
  rw [← originalList_eq]
  apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
  · exact (window_perm_original hm hj hjm).trans (List.mergeSort_perm _ _).symm
  · exact (entry_strictMono hm hj hjm).monotone.ofFn_sorted
  · exact List.sorted_mergeSort' _ _

end Guralnick.Family
