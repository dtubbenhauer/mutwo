import Guralnick.ElementaryCoxeterParabolic
import Guralnick.FamilyInversions

/-! # Inversions after choosing an omitted cyclic cut
The cut determines an honest linear ordering of the residue set. For windows
in its finite stabilizer, affine inversions are exactly inversions in this
ordering; winding is eliminated by the proved potential formula.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterCutLength
open Hecke ParabolicWeb ElementaryCoxeterParabolic
open scoped BigOperators

/-- Zero-based position in the fundamental interval starting at cut `a`. -/
def cutRank {n : ℕ} (a i : Fin n) : Fin n :=
  ⟨if i.val<a.val then i.val+n-a.val else i.val-a.val, by
    have ha:=a.isLt
    have hi:=i.isLt
    split_ifs <;> omega⟩

theorem cutRank_injective {n : ℕ} (a : Fin n) : Function.Injective (cutRank a) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [cutRank] at hh
  have ha:=a.isLt
  have hi:=i.isLt
  have hj:=j.isLt
  split_ifs at hh <;> omega

def cutEquiv {n : ℕ} (a : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (cutRank a) ⟨cutRank_injective a,Finite.surjective_of_injective (cutRank_injective a)⟩

/-- An unordered pair changes its order in the selected fundamental interval. -/
def crossing {n : ℕ} (a : Fin n) (w : AffinePermutation n) (i j : Fin n) : Prop :=
  (cutRank a i < cutRank a j ∧ cutRank a (w.residue j)<cutRank a (w.residue i)) ∨
  (cutRank a j < cutRank a i ∧ cutRank a (w.residue i)<cutRank a (w.residue j))

instance {n : ℕ} (a : Fin n) (w : AffinePermutation n) (i j : Fin n) :
    Decidable (crossing a w i j) := inferInstanceAs (Decidable (_ ∨ _))

theorem crossing_symm {n : ℕ} (a : Fin n) (w : AffinePermutation n) (i j : Fin n) :
    crossing a w i j ↔ crossing a w j i := by unfold crossing; tauto

@[simp] theorem crossing_self {n : ℕ} (a : Fin n) (w : AffinePermutation n) (i : Fin n) :
    ¬crossing a w i i := by simp [crossing]

set_option maxHeartbeats 800000 in
theorem inversion_pair {n : ℕ} (a : Fin n) (w : AffinePermutation n)
    (hw : w ∈ cutSubgroup a) (i j : Fin n) (hij : i < j) :
    ((w.entry j-w.entry i)/(n : ℤ)).natAbs = if crossing a w i j then 1 else 0 := by
  classical
  rw [Family.entry_difference_div (Fin.pos a),hw j,hw i]
  have hi:=i.isLt
  have hj:=j.isLt
  have ha:=a.isLt
  have hri:=(w.residue i).isLt
  have hrj:=(w.residue j).isLt
  have hij' : i.val<j.val := hij
  have hrne : (w.residue i).val≠(w.residue j).val := by
    intro h
    exact (ne_of_lt hij) (w.residue.injective (Fin.ext h))
  simp only [cutPotential,crossing,Fin.lt_def,cutRank]
  split_ifs <;> norm_num <;> omega

/-- Symmetric pair counting removes the arbitrary numerical order of residues. -/
theorem twice_inversionCount {n : ℕ} (a : Fin n) (w : AffinePermutation n)
    (hw : w ∈ cutSubgroup a) :
    2*w.inversionCount = ∑ i : Fin n, ∑ j : Fin n, if crossing a w i j then 1 else 0 := by
  classical
  have hp (i j : Fin n) :
      (if crossing a w i j then 1 else 0) =
      (if i < j then if crossing a w i j then 1 else 0 else 0) +
      (if j < i then if crossing a w j i then 1 else 0 else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge (le_of_lt h)]
    · subst j; simp
    · simp [h,not_lt_of_ge (le_of_lt h),crossing_symm a w i j]
  have hsum : w.inversionCount = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then if crossing a w i j then 1 else 0 else 0 := by
    unfold AffinePermutation.inversionCount
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [if_pos h]
      exact inversion_pair a w hw i j h
    · simp only [if_neg h]
  have ht := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun i _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun j _ => hp i j))
  simp only [Finset.sum_add_distrib] at ht
  have hs : (∑ i : Fin n, ∑ j : Fin n,
      if j < i then if crossing a w j i then 1 else 0 else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then if crossing a w i j then 1 else 0 else 0 :=
    Finset.sum_comm
  rw [hs,←hsum] at ht
  omega

#print axioms twice_inversionCount
end Guralnick.ElementaryCoxeterCutLength
