import Guralnick.ElementaryCoxeterCutLength
import Guralnick.ElementaryCoxeterDiagram

/-! # Actual change of the affine cyclic cut
The rotation is a group automorphism of balanced windows, retaining the
winding correction. It permutes the simple windows, so its length invariance
follows from reduced words. On the cut stabilizer it removes all winding.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterRotation
open Hecke ParabolicWeb ElementaryCoxeterParabolic ElementaryCoxeterCutLength
open scoped BigOperators

/-- Change residue labels and integer lifts. The winding correction is a
coboundary and therefore preserves the balanced sum. -/
def gauge {n : ℕ} (τ : Equiv.Perm (Fin n)) (t : Fin n → ℤ)
    (w : AffinePermutation n) : AffinePermutation n where
  residue := τ*w.residue*τ.symm
  winding r := w.winding (τ.symm r)-t (w.residue (τ.symm r))+t (τ.symm r)
  balanced := by
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [Equiv.sum_comp τ.symm w.winding,Equiv.sum_comp τ.symm (fun i => t (w.residue i)),
      Equiv.sum_comp τ.symm t,Equiv.sum_comp w.residue t,w.balanced]
    ring

@[simp] theorem gauge_residue {n : ℕ} (τ : Equiv.Perm (Fin n)) (t : Fin n → ℤ)
    (w : AffinePermutation n) (i : Fin n) :
    (gauge τ t w).residue (τ i)=τ (w.residue i) := by simp [gauge,Equiv.Perm.mul_apply]

@[simp] theorem gauge_winding {n : ℕ} (τ : Equiv.Perm (Fin n)) (t : Fin n → ℤ)
    (w : AffinePermutation n) (i : Fin n) :
    (gauge τ t w).winding (τ i)=w.winding i-t (w.residue i)+t i := by simp [gauge]

theorem gauge_mul {n : ℕ} (τ : Equiv.Perm (Fin n)) (t : Fin n → ℤ)
    (u v : AffinePermutation n) : gauge τ t (u*v)=gauge τ t u*gauge τ t v := by
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro r
    simp [gauge,Equiv.Perm.mul_apply]
  · funext r
    simp only [gauge,AffinePermutation.mul_winding,AffinePermutation.mul_residue,
      Equiv.Perm.mul_apply,Equiv.symm_apply_apply]
    ring

theorem gauge_inverse {n : ℕ} (τ : Equiv.Perm (Fin n)) (t : Fin n → ℤ)
    (w : AffinePermutation n) : gauge τ.symm (fun i => -t (τ.symm i)) (gauge τ t w)=w := by
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    simp [gauge,Equiv.Perm.mul_apply]
  · funext i
    simp [gauge,Equiv.Perm.mul_apply]
    ring

def gaugeEquiv {n : ℕ} (τ : Equiv.Perm (Fin n)) (t : Fin n → ℤ) :
    AffinePermutation n ≃* AffinePermutation n where
  toFun := gauge τ t
  invFun := gauge τ.symm (fun i => -t (τ.symm i))
  left_inv := gauge_inverse τ t
  right_inv w := by
    have h := gauge_inverse τ.symm (fun i => -t (τ.symm i)) w
    simpa using h
  map_mul' := gauge_mul τ t

def rotation {n : ℕ} (a : Fin n) : AffinePermutation n ≃* AffinePermutation n :=
  gaugeEquiv (cutEquiv a) (cutPotential a)

theorem cutRank_int {n : ℕ} (a i : Fin n) :
    ((cutRank a i).val : ℤ)=(i.val : ℤ)+n*cutPotential a i-a.val := by
  have ha:=a.isLt
  have hi:=i.isLt
  simp only [cutRank,cutPotential]
  split_ifs <;> push_cast <;> omega

theorem rotation_entry {n : ℕ} (a : Fin n) (w : AffinePermutation n) (i : Fin n) :
    (rotation a w).entry (cutEquiv a i)=w.entry i+n*cutPotential a i-a.val := by
  change (gauge (cutEquiv a) (cutPotential a) w).entry (cutEquiv a i)=_
  simp only [AffinePermutation.entry,gauge_residue,gauge_winding]
  change ((cutRank a (w.residue i)).val : ℤ)+1+_= _
  rw [cutRank_int]
  ring

set_option maxHeartbeats 3000000 in
theorem simpleEntry_rotation {n : ℕ} (a s i : Fin n) :
    simpleEntry (cutEquiv a s) (cutEquiv a i)=
      simpleEntry s i+n*cutPotential a i-a.val := by
  have ha:=a.isLt
  have hs:=s.isLt
  have hi:=i.isLt
  have hei : cutEquiv a i=cutEquiv a s ↔ i=s := (cutEquiv a).injective.eq_iff
  change simpleEntry (cutRank a s) (cutRank a i)=_
  have he : cutRank a i=cutRank a s ↔ i=s := (cutRank_injective a).eq_iff
  simp only [simpleEntry,he,cutRank,cutPotential,Fin.ext_iff]
  split_ifs <;> push_cast <;> omega

theorem rotation_simple {n : ℕ} [NeZero n] (c : WindowCoxeter n) (a s : Fin n) :
    rotation a (c.system.simple s)=c.system.simple (cutEquiv a s) := by
  apply FiniteSource.affine_ext_entry
  funext r
  obtain ⟨i,rfl⟩ := (cutEquiv a).surjective r
  rw [rotation_entry,c.simple_window,c.simple_window,simpleEntry_rotation]

theorem rotation_length {n : ℕ} [NeZero n] (c : WindowCoxeter n) (a : Fin n)
    (w : AffinePermutation n) : c.system.length (rotation a w)=c.system.length w :=
  ElementaryCoxeterDiagram.length_map (rotation a) (cutEquiv a) (rotation_simple c a) w

theorem rotation_zero_winding {n : ℕ} (a : Fin n) (w : AffinePermutation n)
    (hw : w ∈ cutSubgroup a) : (rotation a w).winding=0 := by
  funext r
  obtain ⟨i,rfl⟩ := (cutEquiv a).surjective r
  change (gauge (cutEquiv a) (cutPotential a) w).winding (cutEquiv a i)=0
  rw [gauge_winding,hw]
  ring


theorem rotation_right_descent {n : ℕ} [NeZero n] (c : WindowCoxeter n)
    (a : Fin n) (w : AffinePermutation n) (s : Fin n) :
    c.system.IsRightDescent (rotation a w) (cutEquiv a s) ↔ c.system.IsRightDescent w s := by
  unfold CoxeterSystem.IsRightDescent
  rw [←rotation_simple c a,←map_mul,rotation_length,rotation_length]

/-- Every omitted cut remains an omitted cut after actual affine rotation. -/
theorem rotation_mem_cut {n : ℕ} [NeZero n] (c : WindowCoxeter n)
    (a : Fin n) (I : Index n) (w : subgroup c I) (b : Fin n) (hb : b ∉ I.val) :
    rotation a w.val ∈ cutSubgroup (cutEquiv a b) := by
  have h : subgroup c I ≤ (cutSubgroup (cutEquiv a b)).comap (rotation a).toMonoidHom := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨s,hs,rfl⟩
    change rotation a (c.system.simple s) ∈ cutSubgroup (cutEquiv a b)
    rw [rotation_simple]
    have hne : cutEquiv a s≠cutEquiv a b := fun he => hb ((cutEquiv a).injective he ▸ hs)
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    exact simple_mem_cut c (cutEquiv a b) (cutEquiv a s) hne
  exact h w.property

#print axioms rotation_length
#print axioms rotation_mem_cut
end Guralnick.ElementaryCoxeterRotation
