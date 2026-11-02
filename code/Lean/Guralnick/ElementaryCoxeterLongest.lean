import Guralnick.ElementaryCoxeterLengthBound
import Guralnick.ElementaryCoxeterPacketPermutation

/-!
# Longest-element uniqueness and the universal parabolic descent bound

The packet labels here count omitted cuts; no choice of a composition is
needed. A subgroup element preserves every label. A window with all the
parabolic right descents decreases on each label interval, even when its
winding is nonzero. These two facts yield uniqueness in the subgroup and
the lower length bound for arbitrary affine windows.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterLongest
open Hecke ParabolicWeb ElementaryCoxeterParabolic ElementaryCoxeterCutLength
open ElementaryCoxeterRotation ElementaryCoxeterOrderedBlocks
open scoped BigOperators

def omittedCuts {n : ℕ} (a : Fin n) (I : Index n) : Finset (Fin n) :=
  I.valᶜ.image (cutEquiv a)

def label {n : ℕ} (a : Fin n) (I : Index n) (i : Fin n) : ℕ :=
  ((omittedCuts a I).filter (fun r => r  ≤  i)).card

theorem label_monotone {n : ℕ} (a : Fin n) (I : Index n) : Monotone (label a I) := by
  intro i j hij
  apply Finset.card_le_card
  intro r hr
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2.trans hij⟩

theorem label_eq_not_mem {n : ℕ} (a : Fin n) (I : Index n) (i j : Fin n)
    (hij : i<j) (h : label a I i=label a I j) : j∉omittedCuts a I := by
  intro hj
  have hs : (omittedCuts a I).filter (fun r => r  ≤  i) ⊂
      (omittedCuts a I).filter (fun r => r  ≤  j) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro r hr
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,
        (Finset.mem_filter.mp hr).2.trans (le_of_lt hij)⟩
    · intro he
      have hm : j∈(omittedCuts a I).filter (fun r => r  ≤  j) := by simp [hj]
      rw [←he] at hm
      exact (not_le_of_gt hij) (Finset.mem_filter.mp hm).2
  exact (ne_of_lt (Finset.card_lt_card hs)) h

theorem selected_edge {n : ℕ} (a : Fin n) (I : Index n) (i j : Fin n)
    (hij : i<j) (h : label a I i=label a I j) : (cutEquiv a).symm j∈I.val := by
  classical
  by_contra hs
  apply label_eq_not_mem a I i j hij h
  exact Finset.mem_image.mpr ⟨(cutEquiv a).symm j,Finset.mem_compl.mpr hs,
    (cutEquiv a).apply_symm_apply j⟩

theorem rotated_zero_winding {n : ℕ} (c : WindowCoxeter n) (a : Fin n) (I : Index n)
    (ha : a∉I.val) (w : subgroup c I) : (rotation a w.val).winding=0 :=
  rotation_zero_winding a w.val (subgroup_le_cut c I a ha w.property)

theorem label_preserved {n : ℕ} [NeZero n] (c : WindowCoxeter n) (a : Fin n)
    (I : Index n) (ha : a∉I.val) (w : subgroup c I) (i : Fin n) :
    label a I ((rotation a w.val).residue i)=label a I i := by
  have hw := rotated_zero_winding c a I ha w
  apply congrArg Finset.card
  apply Finset.ext
  intro r
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hr
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hr
  have hc := rotation_mem_cut c a I w b (Finset.mem_compl.mp hb)
  have he := hc i
  rw [hw] at he
  simp only [Pi.zero_apply,cutPotential] at he
  change (cutEquiv a b).val ≤ ((rotation a w.val).residue i).val ↔
    (cutEquiv a b).val ≤ i.val
  split_ifs at he <;> omega

theorem label_entry_descent {n : ℕ} [NeZero n] (c : WindowCoxeter n) (a : Fin n)
    (I : Index n) (w : AffinePermutation n)
    (hd : ∀ s, s∈I.val → c.system.IsRightDescent w s)
    (i j : Fin n) (hij : i.val+1=j.val) (hp : label a I i=label a I j) :
    (rotation a w).entry j<(rotation a w).entry i := by
  have hs := selected_edge a I i j (by change i.val<j.val; omega) hp
  have h := (rotation_right_descent c a w ((cutEquiv a).symm j)).mpr (hd _ hs)
  simp only [Equiv.apply_symm_apply] at h
  exact (c.finite_descent (rotation a w) i j hij).mp h

theorem label_residue_descent {n : ℕ} [NeZero n] (c : WindowCoxeter n) (a : Fin n)
    (I : Index n) (ha : a∉I.val) (w : subgroup c I)
    (hd : ∀ s, s∈I.val → c.system.IsRightDescent w.val s)
    (i j : Fin n) (hij : i.val+1=j.val) (hp : label a I i=label a I j) :
    (rotation a w.val).residue j<(rotation a w.val).residue i := by
  have h := label_entry_descent c a I w.val hd i j hij hp
  simpa [AffinePermutation.entry,rotated_zero_winding c a I ha w] using h

theorem exists_omitted {n : ℕ} (I : Index n) : ∃ a : Fin n,a∉I.val := by
  classical
  by_contra h
  apply I.property
  apply Finset.eq_univ_of_forall
  simpa using h

/-- Every affine element with all the parabolic right descents has length
at least that of the actual finite parabolic longest element. -/
theorem length_ge_of_right_descents {n : ℕ} (c : WindowCoxeter n) (I : Index n)
    (D : LongestData c I) (w : AffinePermutation n)
    (hd : ∀ s,s∈I.val → c.system.IsRightDescent w s) :
    c.system.length D.longest.val ≤ c.system.length w := by
  obtain ⟨a,ha⟩ := exists_omitted I
  letI : NeZero n := ⟨Nat.ne_of_gt (Fin.pos a)⟩
  have hD := twice_length c (Fin.pos a) (rotation a D.longest.val)
    (rotated_zero_winding c a I ha D.longest) (label a I) (label_monotone a I)
    (label_preserved c a I ha D.longest)
    (label_residue_descent c a I ha D.longest (ElementaryCoxeterFinite.longest_right_descent c I D))
  have hw := ElementaryCoxeterLengthBound.twice_length_lower c (Fin.pos a) (rotation a w)
    (label a I) (label_monotone a I) (label_entry_descent c a I w hd)
  rw [rotation_length] at hD hw
  omega

/-- Within the actual generated subgroup, all generating right descents
characterize its longest element uniquely. -/
theorem eq_longest_of_right_descents {n : ℕ} (c : WindowCoxeter n) (I : Index n)
    (D : LongestData c I) (w : subgroup c I)
    (hd : ∀ s,s∈I.val → c.system.IsRightDescent w.val s) : w.val=D.longest.val := by
  obtain ⟨a,ha⟩ := exists_omitted I
  letI : NeZero n := ⟨Nat.ne_of_gt (Fin.pos a)⟩
  have hσ := ElementaryCoxeterPackets.fiber_preserving_strictAnti_unique (label a I)
    (rotation a w.val).residue (rotation a D.longest.val).residue
    (label_preserved c a I ha w) (label_preserved c a I ha D.longest)
    (fun i j hp hij => reverse_in_packet (label a I) (label_monotone a I)
      (rotation a w.val).residue (label_residue_descent c a I ha w hd) i j hij hp)
    (fun i j hp hij => reverse_in_packet (label a I) (label_monotone a I)
      (rotation a D.longest.val).residue
      (label_residue_descent c a I ha D.longest (ElementaryCoxeterFinite.longest_right_descent c I D))
      i j hij hp)
  apply (rotation a).injective
  apply AffinePermutation.ext hσ
  rw [rotated_zero_winding c a I ha w,rotated_zero_winding c a I ha D.longest]

/-- Every other member of the finite parabolic has strictly smaller length. -/
theorem length_lt_longest {n : ℕ} (c : WindowCoxeter n) (I : Index n)
    (D : LongestData c I) (w : subgroup c I) (hw : w.val≠D.longest.val) :
    c.system.length w.val<c.system.length D.longest.val := by
  have hmax := D.length_max w
  apply lt_of_le_of_ne hmax
  intro he
  apply hw
  apply eq_longest_of_right_descents c I D w
  intro s hs
  have hsmem : c.system.simple s∈subgroup c I := Subgroup.subset_closure ⟨s,hs,rfl⟩
  have h := D.length_max (w*⟨c.system.simple s,hsmem⟩)
  change c.system.length (w.val*c.system.simple s) ≤ c.system.length D.longest.val at h
  rw [←he] at h
  exact lt_of_le_of_ne h (c.system.length_mul_simple_ne _ _)

#print axioms length_ge_of_right_descents
#print axioms eq_longest_of_right_descents
#print axioms length_lt_longest
end Guralnick.ElementaryCoxeterLongest
