import Guralnick.ElementaryCoxeterRotation

/-! # A maximal permutation inside ordered packets
Monotone packet labels and the adjacent descent rule force reversal within
each packet and forbid inversions between packets. The argument is uniform
in the number and sizes of the packets.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterOrderedBlocks
open Hecke ParabolicWeb ElementaryCoxeterParabolic ElementaryCoxeterCutLength
open scoped BigOperators

variable {n : ℕ} {β : Type*} [LinearOrder β]
variable (p : Fin n → β) (hp : Monotone p) (σ : Equiv.Perm (Fin n))
variable (hpres : ∀ i, p (σ i)=p i)
variable (hd : ∀ i j : Fin n, i.val+1=j.val → p i=p j → σ j<σ i)
include hp hd in

theorem reverse_in_packet (i j : Fin n) (hij : i<j) (hpij : p i=p j) : σ j<σ i := by
  have aux (r : ℕ) : ∀ i j : Fin n, j.val=r → i<j → p i=p j → σ j<σ i := by
    induction r with
    | zero => intro i j hj hij hpij; have : i.val<j.val:=hij; omega
    | succ r ih =>
      intro i j hj hij hpij
      have hij' : i.val<j.val:=hij
      let b : Fin n := ⟨r,by have := j.isLt; omega⟩
      have hib : i≤b := by change i.val≤r; omega
      have hbj : b≤j := by change r≤j.val; omega
      have hpb : p b=p j := le_antisymm (hp hbj) (by rw [←hpij]; exact hp hib)
      have hlast : σ j<σ b := hd b j (by change r+1=j.val; omega) hpb
      by_cases he : i=b
      · simpa [he] using hlast
      · exact hlast.trans (ih i b rfl (lt_of_le_of_ne hib he) (hpij.trans hpb.symm))
  exact aux j.val i j rfl hij hpij

include hp hpres hd in
theorem inversion_iff_same_packet (i j : Fin n) (hij : i<j) :
    σ j<σ i ↔ p i=p j := by
  constructor
  · intro h
    apply le_antisymm (hp (le_of_lt hij))
    simpa only [hpres] using hp (le_of_lt h)
  · exact reverse_in_packet p hp σ hd i j hij

include hp hpres hd in
theorem crossing_iff_same_packet (hn : 0<n) (w : AffinePermutation n)
    (hσ : w.residue=σ) (i j : Fin n) :
    crossing (⟨0,hn⟩ : Fin n) w i j ↔ p i=p j ∧ i≠j := by
  have hr (x : Fin n) : cutRank (⟨0,hn⟩ : Fin n) x=x := by
    apply Fin.ext
    simp [cutRank]
  simp only [crossing,hr,hσ]
  constructor
  · rintro (⟨hij,hσij⟩|⟨hji,hσji⟩)
    · exact ⟨(inversion_iff_same_packet p hp σ hpres hd i j hij).mp hσij,ne_of_lt hij⟩
    · exact ⟨((inversion_iff_same_packet p hp σ hpres hd j i hji).mp hσji).symm,ne_of_gt hji⟩
  · rintro ⟨hij,hne⟩
    rcases lt_or_gt_of_ne hne with hlt|hlt
    · exact Or.inl ⟨hlt,(inversion_iff_same_packet p hp σ hpres hd i j hlt).mpr hij⟩
    · exact Or.inr ⟨hlt,(inversion_iff_same_packet p hp σ hpres hd j i hlt).mpr hij.symm⟩

/-- The length of a zero-winding permutation decreasing within each packet
is half the number of ordered distinct pairs in a packet. -/
theorem twice_length (c : WindowCoxeter n) (hn : 0<n) (w : AffinePermutation n)
    (hw : w.winding=0) (p : Fin n → β) (hp : Monotone p)
    (hpres : ∀ i, p (w.residue i)=p i)
    (hd : ∀ i j : Fin n, i.val+1=j.val → p i=p j → w.residue j<w.residue i) :
    2*c.system.length w = ∑ i : Fin n, ∑ j : Fin n, if p i=p j ∧ i≠j then 1 else 0 := by
  classical
  rw [c.length_formula]
  have hcut : w ∈ cutSubgroup (⟨0,hn⟩ : Fin n) := by
    intro i
    simp [hw,cutPotential]
  rw [twice_inversionCount (⟨0,hn⟩ : Fin n) w hcut]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [crossing_iff_same_packet p hp w.residue hpres hd hn w rfl i j]

#print axioms twice_length
end Guralnick.ElementaryCoxeterOrderedBlocks
