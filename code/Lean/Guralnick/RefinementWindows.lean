import Guralnick.CanonicalSpherical
import Guralnick.HeckeRefinement

/-!
# Actual affine indices for the output refinements

The two one-line refinements are simple left ascents of the actual family
permutation. The full-spherical refinement has the same winding data and
therefore the same finite left coset. Its length shift is computed from the
proved window lengths, not supplied as a refinement normalization.
-/

noncomputable section
namespace Guralnick.RefinementWindows
open Hecke ParabolicWeb

theorem inverse_entry_at_residue {n : ℕ} (w : AffinePermutation n) (i : Fin n) :
    w⁻¹.entry (w.residue i) = (i.val : ℤ)+1-n*w.winding i := by
  simp [AffinePermutation.inv_eq_inverse, AffinePermutation.inverse,
    AffinePermutation.entry, mul_neg, sub_eq_add_neg]

theorem upper_inverse_entry_at_residue {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (i : Fin (2*m+1)) :
    (Family.upper hm hj hjm)⁻¹.entry ((Family.affine hm hj hjm).residue i) =
      (2*m+1 : ℕ) - (i.val : ℤ) - (2*m+1 : ℕ)*Family.winding m j i := by
  have h := inverse_entry_at_residue (Family.upper hm hj hjm) i.rev
  simp only [Family.upper, AffinePermutation.mul_residue,
    AffinePermutation.mul_winding, AffinePermutation.longest_residue,
    AffinePermutation.longest_winding, Pi.zero_apply, zero_add,
    Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev,
    show (Family.affine hm hj hjm).winding = Family.winding m j from rfl,
    Fin.val_rev] at h
  rw [Nat.cast_sub (show i.val+1 ≤ 2*m+1 by omega), Nat.cast_add,
    Nat.cast_one] at h
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  convert h using 1 <;> ring

theorem middle_residue {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Family.affine hm hj hjm).residue ⟨m, by omega⟩ = ⟨m, by omega⟩ := by
  apply Fin.ext
  have h := Family.residue_value hm hj hjm ⟨m, by omega⟩
  simp [Weights.smallResidue] at h
  exact_mod_cast h

theorem left_mark_residue {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Family.affine hm hj hjm).residue ⟨j-1, by omega⟩ = ⟨m+1, by omega⟩ := by
  apply Fin.ext
  have h := Family.residue_value hm hj hjm ⟨j-1, by omega⟩
  have hjm' : j-1 < m := by omega
  have hj' : j-1+1=j := by omega
  simp [Weights.smallResidue, Weights.leftResidue, hjm', hj'] at h
  exact_mod_cast h

theorem right_mark_residue {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Family.affine hm hj hjm).residue ⟨2*m+1-j, by omega⟩ = ⟨m-1, by omega⟩ := by
  apply Fin.ext
  have h := Family.residue_value hm hj hjm ⟨2*m+1-j, by omega⟩
  have hgt : m < 2*m+1-j := by omega
  have hsub : 2*m-(2*m+1-j)=j-1 := by omega
  have hj' : j-1+1=j := by omega
  simp [Weights.smallResidue, Weights.leftResidue, Nat.not_lt.mpr hgt.le,
    Nat.ne_of_gt hgt, hsub, hj'] at h
  change (Family.residue hm hj hjm ⟨2*m+1-j, by omega⟩).val = m-1
  omega

theorem upper_inverse_middle {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Family.upper hm hj hjm)⁻¹.entry ⟨m, by omega⟩ = (m : ℤ)+1 := by
  have h := upper_inverse_entry_at_residue hm hj hjm ⟨m, by omega⟩
  rw [middle_residue] at h
  have h₁ : ¬m<j := by omega
  have h₂ : ¬2*m+1-j≤m := by omega
  simp [Family.winding, h₁, h₂] at h
  omega

theorem upper_inverse_left_mark {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Family.upper hm hj hjm)⁻¹.entry ⟨m-1, by omega⟩ = (j : ℤ)-(2*m+1 : ℕ) := by
  have h := upper_inverse_entry_at_residue hm hj hjm ⟨2*m+1-j, by omega⟩
  rw [right_mark_residue] at h
  have h₁ : ¬2*m+1-j<j := by omega
  simp only [Family.winding, h₁, if_false, le_refl, if_true, mul_one] at h
  push_cast at h
  omega

theorem upper_inverse_right_mark {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Family.upper hm hj hjm)⁻¹.entry ⟨m+1, by omega⟩ =
      2*(2*m+1 : ℕ)+1-(j : ℤ) := by
  have h := upper_inverse_entry_at_residue hm hj hjm ⟨j-1, by omega⟩
  rw [left_mark_residue] at h
  have h₁ : j-1<j := by omega
  simp only [Family.winding, h₁, if_true, mul_neg, mul_one, sub_neg_eq_add] at h
  push_cast at h
  omega

theorem weak_left_ascent {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2*m+1)) :
    ¬c.system.IsLeftDescent (Family.upper hm hj hjm) ⟨m, by omega⟩ := by
  rw [←c.system.isRightDescent_inv_iff,
    c.finite_descent _ ⟨m-1, by omega⟩ ⟨m, by omega⟩ (by simp; omega),
    upper_inverse_middle, upper_inverse_left_mark]
  omega

theorem strong_left_ascent {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2*m+1)) :
    ¬c.system.IsLeftDescent (Family.upper hm hj hjm) ⟨m+1, by omega⟩ := by
  rw [←c.system.isRightDescent_inv_iff,
    c.finite_descent _ ⟨m, by omega⟩ ⟨m+1, by omega⟩ (by rfl),
    upper_inverse_right_mark, upper_inverse_middle]
  omega

theorem weak_length_shift {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2*m+1)) :
    c.system.length (c.system.simple ⟨m, by omega⟩ * Family.upper hm hj hjm) =
      c.system.length (Family.upper hm hj hjm)+1 :=
  c.system.not_isLeftDescent_iff.mp (weak_left_ascent hm hj hjm c)

theorem strong_length_shift {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2*m+1)) :
    c.system.length (c.system.simple ⟨m+1, by omega⟩ * Family.upper hm hj hjm) =
      c.system.length (Family.upper hm hj hjm)+1 :=
  c.system.not_isLeftDescent_iff.mp (strong_left_ascent hm hj hjm c)

/-- Equal winding data is exactly enough for a finite left permutation to
identify the two actual affine windows. -/
theorem finite_left_of_winding_eq {n : ℕ} (u v : AffinePermutation n)
    (h : u.winding = v.winding) :
    AffinePermutation.finiteEmbedding n (v.residue*u.residue⁻¹) * u = v := by
  apply AffinePermutation.ext
  · simp [AffinePermutation.finiteEmbedding, mul_assoc]
  · funext i
    simpa [AffinePermutation.finiteEmbedding] using congrFun h i

theorem spherical_winding {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Family.upper hm hj hjm).winding = (CanonicalSpherical.index m j).winding := by
  funext i
  simp only [Family.upper, CanonicalSpherical.index, AffinePermutation.mul_winding,
    AffinePermutation.longest_winding, Pi.zero_apply, zero_add,
    CanonicalSpherical.translation_winding hjm]
  rfl

/-- The full-spherical output normalization is the actual length difference. -/
theorem spherical_length_shift {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2*m+1)) :
    (c.system.length (CanonicalSpherical.index m j) : ℤ) -
      c.system.length (Family.upper hm hj hjm) = 2*((m : ℤ)-j)+3 := by
  have h₁ := CanonicalSpherical.index_length_gap hjm c
  have h₂ := Hecke.family_length_gap hm hj hjm c
  unfold gapFormula at h₂
  push_cast at h₂
  omega

end Guralnick.RefinementWindows
