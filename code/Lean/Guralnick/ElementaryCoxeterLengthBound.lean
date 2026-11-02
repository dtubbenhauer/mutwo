import Guralnick.ElementaryCoxeterOrderedBlocks

/-! # A lower length bound from packet descents
The output winding is arbitrary. Every decreasing pair in an input packet
contributes at least one to the actual affine inversion count.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterLengthBound
open Hecke
open scoped BigOperators

variable {n : ℕ} {β γ : Type*} [LinearOrder β] [LinearOrder γ]

theorem decreasing_on_label (p : Fin n → β) (hp : Monotone p) (f : Fin n → γ)
    (hd : ∀ i j : Fin n, i.val+1=j.val → p i=p j → f j<f i)
    (i j : Fin n) (hij : i < j) (hpij : p i=p j) : f j<f i := by
  have aux (r : ℕ) : ∀ i j : Fin n, j.val=r → i < j → p i=p j → f j<f i := by
    induction r with
    | zero => intro i j hj hij hpij; have : i.val<j.val:=hij; omega
    | succ r ih =>
      intro i j hj hij hpij
      have hij' : i.val<j.val:=hij
      let b : Fin n := ⟨r,by have := j.isLt; omega⟩
      have hib : i≤b := by change i.val≤r; omega
      have hbj : b≤j := by change r≤j.val; omega
      have hpb : p b=p j := le_antisymm (hp hbj) (by rw [←hpij]; exact hp hib)
      have hlast : f j<f b := hd b j (by change r+1=j.val; omega) hpb
      by_cases he : i=b
      · simpa [he] using hlast
      · exact hlast.trans (ih i b rfl (lt_of_le_of_ne hib he) (hpij.trans hpb.symm))
  exact aux j.val i j rfl hij hpij

theorem symmetric_pair_count (p : Fin n → β) :
    (∑ i : Fin n, ∑ j : Fin n, if p i=p j ∧ i≠j then 1 else 0) =
      2*(∑ i : Fin n, ∑ j : Fin n, if i < j then if p i=p j then 1 else 0 else 0) := by
  classical
  have hp (i j : Fin n) :
      (if p i=p j ∧ i≠j then (1 : ℕ) else 0)=
      (if i < j then if p i=p j then 1 else 0 else 0)+
      (if j < i then if p j=p i then 1 else 0 else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,ne_of_lt h,not_lt_of_ge (le_of_lt h)]
    · subst j; simp
    · simp [h,ne_of_gt h,not_lt_of_ge (le_of_lt h),eq_comm]
  have ht := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun i _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun j _ => hp i j))
  simp only [Finset.sum_add_distrib] at ht
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then if p j=p i then 1 else 0 else 0)=
      ∑ i : Fin n, ∑ j : Fin n, if i < j then if p i=p j then 1 else 0 else 0 := Finset.sum_comm
  rw [hs] at ht
  omega

theorem twice_length_lower (c : WindowCoxeter n) (hn : 0<n) (w : AffinePermutation n)
    (p : Fin n → β) (hp : Monotone p)
    (hd : ∀ i j : Fin n, i.val+1=j.val → p i=p j → w.entry j<w.entry i) :
    (∑ i : Fin n, ∑ j : Fin n, if p i=p j ∧ i≠j then 1 else 0) ≤ 2*c.system.length w := by
  classical
  rw [symmetric_pair_count p,c.length_formula]
  apply Nat.mul_le_mul_left
  unfold AffinePermutation.inversionCount
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    by_cases h : p i=p j
    · rw [if_pos h]
      have hde := decreasing_on_label p hp w.entry hd i j hij h
      have hq : (w.entry j-w.entry i)/(n : ℤ)<0 :=
        Int.ediv_neg_of_neg_of_pos (by omega) (by omega)
      exact Int.natAbs_pos.mpr (by omega)
    · simp only [if_neg h,Nat.zero_le]
  · simp only [if_neg hij,le_refl]

#print axioms twice_length_lower
end Guralnick.ElementaryCoxeterLengthBound
