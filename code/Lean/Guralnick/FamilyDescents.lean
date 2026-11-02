import Guralnick.RefinementWindows
import Guralnick.CanonicalSchur
import Guralnick.WindowPacketMatrix

/-!
# The actual family's finite left descents

The input winding shift is nondecreasing along each output row. Sorting
therefore places successive residues in increasing positions, and reversal
by w₀ makes their inverse-window entries decrease. This gives the required
left descents without assuming maximality from a displayed matrix.
-/
noncomputable section
namespace Guralnick.Family
open Hecke

/-- The shift rule is nondecreasing between successive residues unless the
edge crosses one of the two output-row boundaries. -/
theorem inputShift_nondecreasing {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (a b : Fin (2*m+1)) (hab : a.val+1=b.val)
    (hbm : b.val ≠ m) (hbm1 : b.val ≠ m+1) :
    familyShift m j (a.val+1) ≤ familyShift m j (b.val+1) := by
  have ha := a.isLt
  have hb := b.isLt
  unfold familyShift
  split_ifs <;> norm_num <;> omega

/-- A nondecreasing pair of original shifts produces a strictly descending
pair in the inverse window of u w₀. -/
theorem upper_inverse_descending_of_shift {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (a b : Fin (2*m+1)) (hab : a < b)
    (hshift : familyShift m j (a.val+1) ≤ familyShift m j (b.val+1)) :
    (upper hm hj hjm)⁻¹.entry b < (upper hm hj hjm)⁻¹.entry a := by
  let u := affine hm hj hjm
  let pa := u.residue.symm a
  let pb := u.residue.symm b
  have hra : u.residue pa = a := u.residue.apply_symm_apply a
  have hrb : u.residue pb = b := u.residue.apply_symm_apply b
  have hwa : winding m j pa = familyShift m j (a.val+1) := by
    have hh := winding_eq_inputShift hm hj hjm pa
    change winding m j pa = familyShift m j ((u.residue pa).val+1) at hh
    rwa [hra] at hh
  have hwb : winding m j pb = familyShift m j (b.val+1) := by
    have hh := winding_eq_inputShift hm hj hjm pb
    change winding m j pb = familyShift m j ((u.residue pb).val+1) at hh
    rwa [hrb] at hh
  have hua : u.entry pa = originalEntry m j a := by
    have hh := entry_eq_original hm hj hjm pa
    change u.entry pa = originalEntry m j (u.residue pa) at hh
    rwa [hra] at hh
  have hub : u.entry pb = originalEntry m j b := by
    have hh := entry_eq_original hm hj hjm pb
    change u.entry pb = originalEntry m j (u.residue pb) at hh
    rwa [hrb] at hh
  have hN : (0 : ℤ) ≤ (2*m+1 : ℕ) := by omega
  have hmul := mul_le_mul_of_nonneg_left hshift hN
  have hue : u.entry pa < u.entry pb := by
    rw [hua,hub]
    unfold originalEntry
    have hab' : (a.val : ℤ) < b.val := by exact_mod_cast hab
    omega
  have hp : pa < pb := (entry_strictMono hm hj hjm).lt_iff_lt.mp hue
  have hia := RefinementWindows.upper_inverse_entry_at_residue hm hj hjm pa
  change (upper hm hj hjm)⁻¹.entry (u.residue pa) =
    (2*m+1 : ℕ) - (pa.val : ℤ) - (2*m+1 : ℕ)*winding m j pa at hia
  rw [hra,hwa] at hia
  have hib := RefinementWindows.upper_inverse_entry_at_residue hm hj hjm pb
  change (upper hm hj hjm)⁻¹.entry (u.residue pb) =
    (2*m+1 : ℕ) - (pb.val : ℤ) - (2*m+1 : ℕ)*winding m j pb at hib
  rw [hrb,hwb] at hib
  rw [hia,hib]
  have hp' : (pa.val : ℤ) < pb.val := by exact_mod_cast hp
  omega

/-- Every required finite output generator is an actual left descent. -/
theorem upper_finite_left_descent {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2*m+1)) (a b : Fin (2*m+1)) (hab : a.val+1=b.val)
    (hbm : b.val ≠ m) (hbm1 : b.val ≠ m+1) :
    c.system.IsLeftDescent (upper hm hj hjm) b := by
  rw [← c.system.isRightDescent_inv_iff,c.finite_descent _ a b hab]
  exact upper_inverse_descending_of_shift hm hj hjm a b (by omega)
    (inputShift_nondecreasing hm hj hjm a b hab hbm hbm1)

/-- The actual upper endpoint has only the three inverse-winding packets. -/
theorem upper_supported {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    WindowPacketMatrix.Supported (upper hm hj hjm) := by
  intro i
  have hw : ∀ q, -1 ≤ (upper hm hj hjm).winding q ∧
      (upper hm hj hjm).winding q ≤ 1 := by
    intro q
    simp only [upper,AffinePermutation.mul_winding,AffinePermutation.longest_winding,
      Pi.zero_apply,zero_add,AffinePermutation.longest_residue,Fin.revPerm_apply]
    change -1 ≤ winding m j q.rev ∧ winding m j q.rev ≤ 1
    unfold winding
    split_ifs <;> norm_num
  change -1 ≤ -(upper hm hj hjm).winding ((upper hm hj hjm).residue.symm i) ∧
    -(upper hm hj hjm).winding ((upper hm hj hjm).residue.symm i) ≤ 1
  have h := hw ((upper hm hj hjm).residue.symm i)
  omega

/-- The stated family really is the maximal representative for the
prescribed output and fixed full spherical source parabolics. -/
theorem upper_doubleMaximal {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2*m+1)) :
    CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output m)
      (ParabolicWeb.Family.source m) (upper hm hj hjm) := by
  constructor
  · intro b hb
    have hbs : b.val ≠ 0 ∧ b.val ≠ m ∧ b.val ≠ m+1 := by
      simpa [ParabolicWeb.Family.output,ParabolicWeb.Family.outputSet,
        ParabolicWeb.Family.sourceSet,ParabolicWeb.Family.cyclicSet] using hb
    let a : Fin (2*m+1) := ⟨b.val-1,by omega⟩
    exact upper_finite_left_descent hm hj hjm c a b (by dsimp [a]; omega) hbs.2.1 hbs.2.2
  · intro b hb
    have hb0 : b.val ≠ 0 := by
      simpa [ParabolicWeb.Family.source,ParabolicWeb.Family.sourceSet] using hb
    let a : Fin (2*m+1) := ⟨b.val-1,by omega⟩
    exact Hecke.upper_all_finite_right_descents hm hj hjm c a b (by dsimp [a]; omega)

end Guralnick.Family
