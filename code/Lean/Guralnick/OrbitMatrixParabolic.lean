import Guralnick.OrbitMatrixSortedWindows
import Guralnick.ElementaryCoxeterPackets
import Guralnick.ElementaryCoxeterParabolic
import Guralnick.ElementaryCoxeterFinite

/-! # The literal periodic matrix is unchanged by its finite parabolics -/
noncomputable section
namespace Guralnick.OrbitMatrixElementary
open Hecke ParabolicWeb FiniteBlocks ElementaryCoxeterPackets ElementaryCoxeterParabolic
variable {N : ℕ} [NeZero N]

/-- At cut zero, the omitted affine nodes are exactly the packet partial sums. -/
theorem mem_cuts_zero (A : FiniteBlocks.Composition N) (hA : A.cut.val = 0) (i : Fin N) :
    i ∈ A.cuts ↔ i.val ∈ A.packets.scanl (·+·) 0 := by
  unfold FiniteBlocks.Composition.cuts
  rw [hA]
  simp only [List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨s,hs,he⟩
    have hle := scanl_le_sum A.packets hs
    rw [A.total] at hle
    have hi : s%N=i.val := congrArg Fin.val he
    by_cases hn : s=N
    · have hi0 : i.val=0 := by simpa [hn] using hi.symm
      rw [hi0]
      exact zero_mem_scanl _
    · have hsN : s<N := by omega
      rw [Nat.mod_eq_of_lt hsN] at hi
      rwa [←hi]
  · intro hi
    exact ⟨i.val,hi,Fin.ext (Nat.mod_eq_of_lt i.isLt)⟩

def rowSet (A : FiniteBlocks.Composition N) (r : Fin A.packets.length) : Finset (Fin N) :=
  Finset.univ.filter fun i =>
    (A.packets.take r.val).sum ≤ i.val ∧ i.val < (A.packets.take (r.val+1)).sum

theorem mem_rowSet (A : FiniteBlocks.Composition N) (r : Fin A.packets.length) (i : Fin N) :
    i ∈ rowSet A r ↔ prefixSum A.packets r ≤ i.val ∧
      i.val < prefixSum A.packets r+A.packets[r.val] := by
  simp only [rowSet,Finset.mem_filter,Finset.mem_univ,true_and,
    List.sum_take_succ _ _ r.isLt,prefixSum]

/-- Omitting the ordinary cut forces zero winding in the parabolic subgroup. -/
theorem parabolic_winding_zero (c : WindowCoxeter N) (I : Index N)
    (h0 : (⟨0,NeZero.pos N⟩ : Fin N) ∉ I.val) (u : subgroup c I) : u.val.winding = 0 := by
  have hu := subgroup_le_cut c I ⟨0,NeZero.pos N⟩ h0 u.property
  funext i
  simpa [cutSubgroup,cutPotential] using hu i

theorem composition_winding_zero (c : WindowCoxeter N) (A : FiniteBlocks.Composition N)
    (hA : A.cut.val=0) (u : subgroup c A.index) : u.val.winding=0 := by
  apply parabolic_winding_zero c A.index _ u
  change (⟨0,NeZero.pos N⟩ : Fin N) ∉ A.cutsᶜ
  simp only [Finset.mem_compl,not_not]
  apply (mem_cuts_zero A hA _).mpr
  exact zero_mem_scanl _

/-- Every omitted cut is preserved by the finite output-parabolic action. -/
theorem residue_cut_iff (c : WindowCoxeter N) (A : FiniteBlocks.Composition N) (hA : A.cut.val=0)
    (u : subgroup c A.index) (a i : Fin N) (ha : a ∈ A.cuts) :
    (u.val.residue i).val < a.val ↔ i.val<a.val := by
  have hu := subgroup_le_cut c A.index a (by simpa [FiniteBlocks.Composition.index] using ha) u.property
  have hz := congrFun (composition_winding_zero c A hA u) i
  have hi := hu i
  change u.val.winding i = cutPotential a (u.val.residue i)-cutPotential a i at hi
  rw [hz] at hi
  simp only [Pi.zero_apply,cutPotential] at hi
  split_ifs at hi <;> omega

/-- Output-parabolic permutations preserve the actual row intervals. -/
theorem residue_row_iff (c : WindowCoxeter N) (A : FiniteBlocks.Composition N) (hA : A.cut.val=0)
    (u : subgroup c A.index) (r : Fin A.packets.length) (i : Fin N) :
    u.val.residue i ∈ rowSet A r ↔ i ∈ rowSet A r := by
  let p := prefixSum A.packets r
  let q := p+A.packets[r.val]
  have hpq : p<q := by have hp:=A.positive _ (List.getElem_mem r.isLt); dsimp [q]; omega
  have hqN : q≤N := by simpa only [q,p,A.total] using prefixSum_end_le A.packets r
  have hpN : p<N := lt_of_lt_of_le hpq hqN
  have hp := residue_cut_iff c A hA u ⟨p,hpN⟩ i
    ((mem_cuts_zero A hA _).mpr (prefixSum_mem_scanl A.packets r))
  rw [mem_rowSet,mem_rowSet]
  change (p ≤ (u.val.residue i).val ∧ (u.val.residue i).val < q) ↔ (p ≤ i.val ∧ i.val < q)
  by_cases hq : q=N
  · have hi := i.isLt
    have hui := (u.val.residue i).isLt
    dsimp only at hp
    omega
  · have hq' : q<N := by omega
    have he := residue_cut_iff c A hA u ⟨q,hq'⟩ i
      ((mem_cuts_zero A hA _).mpr (prefixSum_end_mem_scanl A.packets r))
    dsimp only at hp he
    omega

/-- Both parabolic actions only permute the source of the inverse winding function. -/
theorem double_action_winding (c : WindowCoxeter N) (A : FiniteBlocks.Composition N) (hA : A.cut.val=0)
    (u : subgroup c A.index) (v : subgroup c (CanonicalChains.source (NeZero.pos N)))
    (w : AffinePermutation N) (i : Fin N) :
    ((u.val*w*v.val)⁻¹).winding i = (w⁻¹).winding ((u.val⁻¹).residue i) := by
  have hu := composition_winding_zero c A hA u⁻¹
  have hv := parabolic_winding_zero c (CanonicalChains.source (NeZero.pos N))
    (by simp [CanonicalChains.source,CanonicalChains.omitNode]) v⁻¹
  simp only [mul_inv_rev,AffinePermutation.mul_winding]
  rw [show (u.val⁻¹).winding i = 0 from congrFun hu i]
  rw [show (v.val⁻¹).winding _ = 0 from congrFun hv _]
  simp

theorem supported_double_action (c : WindowCoxeter N) (A : FiniteBlocks.Composition N) (hA : A.cut.val=0)
    (u : subgroup c A.index) (v : subgroup c (CanonicalChains.source (NeZero.pos N)))
    (w : AffinePermutation N) (hw : WindowPacketMatrix.Supported w) :
    WindowPacketMatrix.Supported (u.val*w*v.val) := by
  intro i
  rw [double_action_winding c A hA u v w i]
  exact hw _

theorem entries_double_action (c : WindowCoxeter N) (A : FiniteBlocks.Composition N) (hA : A.cut.val=0)
    (u : subgroup c A.index) (v : subgroup c (CanonicalChains.source (NeZero.pos N)))
    (w : AffinePermutation N) :
    OrbitMatrix.compositionEntries A (u.val*w*v.val) = OrbitMatrix.compositionEntries A w := by
  classical
  funext r col
  have hr (i : Fin N) :
      ((A.packets.take r.val).sum ≤ i.val ∧ i.val < (A.packets.take (r.val+1)).sum) ↔
        ((A.packets.take r.val).sum ≤ ((u.val⁻¹).residue i).val ∧
          ((u.val⁻¹).residue i).val < (A.packets.take (r.val+1)).sum) := by
    simpa only [rowSet,Finset.mem_filter,Finset.mem_univ,true_and] using
      (residue_row_iff c A hA u⁻¹ r i).symm
  unfold OrbitMatrix.compositionEntries
  rw [WindowPacketMatrix.card_filter_sum,WindowPacketMatrix.card_filter_sum]
  let f : Fin N → ℕ := fun i => if
    (A.packets.take r.val).sum ≤ i.val ∧ i.val < (A.packets.take (r.val+1)).sum ∧
      (w⁻¹).winding i=Family.columnShift col then 1 else 0
  have he := Equiv.sum_comp (u.val⁻¹).residue f
  apply Eq.trans _ he
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [f]
  rw [double_action_winding c A hA u v w i]
  simp only [←and_assoc]
  simp only [hr i]

#print axioms entries_double_action
end Guralnick.OrbitMatrixElementary
