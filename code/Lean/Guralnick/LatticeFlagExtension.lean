import Guralnick.LatticeFlagCompletePeriod

/-! # Folding a completed lattice period into an actual full cyclic flag -/
noncomputable section
namespace Guralnick.LatticeFlagExtension
open LaurentLattice LatticeGallery LatticeFlags ElementaryCoxeterCutLength
variable {k : Type} [Field k] {n : ℕ} [NeZero n]
variable {S : Finset (Fin n)} {F : Flag k n S} {b : {i // i∈S}}

def periodIndex (a i : Fin n) : Fin (n+1) :=
  ⟨(cutRank a i).val,by have := (cutRank a i).isLt; omega⟩

theorem periodIndex_same_order (a i j : Fin n) (hij : i ≤ j)
    (hside : (i.val<a.val) ↔ (j.val<a.val)) : periodIndex a i ≤ periodIndex a j := by
  have ha := a.isLt
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val ≤ j.val := hij
  change (cutRank a i).val ≤ (cutRank a j).val
  simp only [cutRank]
  split_ifs <;> omega

theorem periodIndex_across (a i j : Fin n) (hi : ¬i.val<a.val) (hj : j.val<a.val) :
    periodIndex a i ≤ periodIndex a j := by
  have ha := a.isLt
  have hi' := i.isLt
  have hj' := j.isLt
  change (cutRank a i).val ≤ (cutRank a j).val
  simp only [cutRank,if_neg hi,if_pos hj]
  omega

namespace FullPeriodChain
variable (C : FullPeriodChain F b)

theorem base_le_node (i : Fin (n+1)) : F.node b ≤ C.node i := by
  rw [←C.first]
  exact C.ordered (Fin.zero_le _)

theorem node_le_upper (i : Fin (n+1)) : C.node i ≤ up (F.node b) := by
  rw [←C.last]
  exact C.ordered (Fin.le_last _)

def foldNode (i : Fin n) : Lattice k n :=
  if i.val<b.val.val then down (C.node (periodIndex b.val i)) else C.node (periodIndex b.val i)

theorem foldNode_degree (i : Fin n) : degree k n (C.foldNode i)=(i.val : ℤ) := by
  have hi := ElementaryCoxeterRotation.cutRank_int b.val i
  unfold ElementaryCoxeterParabolic.cutPotential at hi
  unfold foldNode
  split_ifs with h
  · rw [down_degree,C.degree_eq]
    change (b.val.val : ℤ)+(cutRank b.val i).val-n=i.val
    rw [if_pos h] at hi
    omega
  · rw [C.degree_eq]
    change (b.val.val : ℤ)+(cutRank b.val i).val=i.val
    rw [if_neg h] at hi
    omega

theorem down_node_le_base (i : Fin (n+1)) : down (C.node i) ≤ F.node b := by
  have h := down_mono (C.node_le_upper i)
  simpa only [down_up] using h

theorem foldNode_order : Monotone C.foldNode := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  unfold foldNode
  split_ifs with hi hj
  · exact down_mono (C.ordered (periodIndex_same_order b.val i j hij (iff_of_true hi hj)))
  · exact (C.down_node_le_base _).trans (C.base_le_node _)
  · omega
  · exact C.ordered (periodIndex_same_order b.val i j hij
      (iff_of_false (by assumption) (by assumption)))

theorem foldNode_cyclic (i j : Fin n) : C.foldNode i ≤ up (C.foldNode j) := by
  unfold foldNode
  split_ifs with hi hj
  · rw [up_down]
    exact (C.down_node_le_base _).trans (C.base_le_node _)
  · exact (C.down_node_le_base _).trans ((C.base_le_node _).trans (le_up _))
  · rw [up_down]
    exact C.ordered (periodIndex_across b.val i j (by assumption) (by assumption))
  · exact (C.node_le_upper _).trans (up_mono (C.base_le_node _))

theorem foldNode_prescribed (i : {i // i∈S}) : C.foldNode i.val=F.node i := by
  unfold foldNode periodIndex
  rw [C.prescribed]
  unfold raised
  split_ifs <;> simp only [down_up]

/-- The folded node sequence satisfies the original absolute degree,
boundary order, and affine cyclic-containment conditions. -/
def fullFlag : Flag k n Finset.univ where
  node i := C.foldNode i.val
  ordered i j hij := C.foldNode_order hij
  cyclic i j := C.foldNode_cyclic i.val j.val
  degree_eq i := C.foldNode_degree i.val

theorem fullFlag_restrict : C.fullFlag.restrict (Finset.subset_univ S)=F := by
  apply LatticeFlags.Flag.ext
  funext i
  exact C.foldNode_prescribed i

end FullPeriodChain

/-- Every nonempty actual partial lattice flag has a full refinement.
The construction uses a retained base, its finite-dimensional period
quotient, actual subspace-chain completion, and the inverse Laurent shift. -/
theorem exists_full_refinement {S : Finset (Fin n)} (F : Flag k n S) (hS : S.Nonempty) :
    ∃ E : Flag k n Finset.univ, E.restrict (Finset.subset_univ S)=F := by
  obtain ⟨b,hb⟩ := hS
  obtain ⟨C⟩ := fullPeriodChain_nonempty F ⟨b,hb⟩
  exact ⟨C.fullFlag,C.fullFlag_restrict⟩

#print axioms exists_full_refinement
end Guralnick.LatticeFlagExtension
