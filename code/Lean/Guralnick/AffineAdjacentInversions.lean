import Guralnick.FamilyInversions

/-! # Adjacent descents from the actual affine inversion sum

Swapping adjacent positions changes only their mutual contribution after
reindexing all other pairs. Euclidean division of distinct affine residues
then proves the exact change in length, including arbitrary winding.
-/
noncomputable section
namespace Guralnick.AffineAdjacentInversions
open scoped BigOperators
variable {n : ℕ}

theorem swap_order (a b i j : Fin n) (hab : a.val+1=b.val)
    (h₁ : ¬(i=a ∧ j=b)) (h₂ : ¬(i=b ∧ j=a)) :
    Equiv.swap a b i < Equiv.swap a b j ↔ i<j := by
  have hi (x y : Fin n) : x≠y → x.val≠y.val := fun h he => h (Fin.ext he)
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    by_cases hja : j=a <;> by_cases hjb : j=b <;>
    simp_all [Equiv.swap_apply_def,Fin.lt_def,-Fin.val_fin_lt] <;> omega

theorem pair_sum_swap (F : Fin n → Fin n → ℕ) (a b : Fin n)
    (hab : a.val+1=b.val) :
    (∑ i : Fin n, ∑ j : Fin n,
      if i<j then F (Equiv.swap a b i) (Equiv.swap a b j) else 0) + F a b =
    (∑ i : Fin n, ∑ j : Fin n, if i<j then F i j else 0) + F b a := by
  classical
  have hlt : a<b := by change a.val<b.val; omega
  have hp (i j : Fin n) :
      (if i<j then F (Equiv.swap a b i) (Equiv.swap a b j) else 0) +
        (if i=b ∧ j=a then F a b else 0) =
      (if Equiv.swap a b i < Equiv.swap a b j then
        F (Equiv.swap a b i) (Equiv.swap a b j) else 0) +
        (if i=a ∧ j=b then F b a else 0) := by
    by_cases h₁ : i=a ∧ j=b
    · obtain ⟨rfl,rfl⟩ := h₁
      simp [hlt,ne_of_lt hlt,ne_of_gt hlt,not_lt_of_ge (le_of_lt hlt)]
    · by_cases h₂ : i=b ∧ j=a
      · obtain ⟨rfl,rfl⟩ := h₂
        simp [hlt,ne_of_lt hlt,ne_of_gt hlt,not_lt_of_ge (le_of_lt hlt)]
      · simp [h₁,h₂,swap_order a b i j hab h₁ h₂]
  have hs := congrArg (fun f : Fin n → Fin n → ℕ => ∑ i, ∑ j, f i j)
    (funext fun i => funext fun j => hp i j)
  simp only [Finset.sum_add_distrib] at hs
  have hd (a b : Fin n) (z : ℕ) : (∑ i : Fin n, ∑ j : Fin n,
      if i=a ∧ j=b then z else 0)=z := by simp [ite_and]
  rw [hd,hd] at hs
  have he : (∑ i : Fin n, ∑ j : Fin n,
      if Equiv.swap a b i < Equiv.swap a b j then
        F (Equiv.swap a b i) (Equiv.swap a b j) else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i<j then F i j else 0 := by
    apply Fintype.sum_equiv (Equiv.swap a b)
    intro i
    apply Fintype.sum_equiv (Equiv.swap a b)
    intro j
    rfl
  rwa [he] at hs

theorem mul_finite_entry (w : AffinePermutation n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (w*AffinePermutation.finiteEmbedding n σ).entry i=w.entry (σ i) := by
  simp [AffinePermutation.entry,AffinePermutation.finiteEmbedding,
    AffinePermutation.compose]

theorem inversion_swap_balance (w : AffinePermutation n) (a b : Fin n)
    (hab : a.val+1=b.val) :
    (w*AffinePermutation.finiteEmbedding n (Equiv.swap a b)).inversionCount +
      ((w.entry b-w.entry a)/(n : ℤ)).natAbs =
    w.inversionCount + ((w.entry a-w.entry b)/(n : ℤ)).natAbs := by
  simpa only [AffinePermutation.inversionCount,mul_finite_entry] using
    pair_sum_swap (fun i j => ((w.entry j-w.entry i)/(n : ℤ)).natAbs) a b hab

theorem opposite_division (w : AffinePermutation n) (a b : Fin n) (hab : a≠b) :
    (w.entry b-w.entry a)/(n : ℤ)+(w.entry a-w.entry b)/(n : ℤ)= -1 := by
  rw [Family.entry_difference_div (Fin.pos a),Family.entry_difference_div (Fin.pos a)]
  have hne : (w.residue a).val≠(w.residue b).val :=
    fun h => hab (w.residue.injective (Fin.ext h))
  split_ifs <;> omega

theorem inversion_swap_lt_iff (w : AffinePermutation n) (a b : Fin n)
    (hab : a.val+1=b.val) :
    (w*AffinePermutation.finiteEmbedding n (Equiv.swap a b)).inversionCount < w.inversionCount ↔
      w.entry b<w.entry a := by
  have hne : a≠b := fun h => by have hv := congrArg Fin.val h; omega
  have hb := inversion_swap_balance w a b hab
  have hd := opposite_division w a b hne
  have hn : (0 : ℤ)<n := by exact_mod_cast Fin.pos a
  have hsign := Int.ediv_nonneg_iff_of_pos (a:=w.entry b-w.entry a) hn
  by_cases h : w.entry b<w.entry a
  · have hq : (w.entry b-w.entry a)/(n : ℤ)<0 :=
      Int.ediv_neg_of_neg_of_pos (by omega) hn
    have hq' : 0≤(w.entry a-w.entry b)/(n : ℤ) := by omega
    have h₁ := Int.natCast_natAbs ((w.entry b-w.entry a)/(n : ℤ))
    have h₂ := Int.natCast_natAbs ((w.entry a-w.entry b)/(n : ℤ))
    rw [abs_of_neg hq] at h₁
    rw [abs_of_nonneg hq'] at h₂
    constructor <;> intro <;> omega
  · have hq : 0≤(w.entry b-w.entry a)/(n : ℤ) := hsign.mpr (by omega)
    have hq' : (w.entry a-w.entry b)/(n : ℤ)<0 := by omega
    have h₁ := Int.natCast_natAbs ((w.entry b-w.entry a)/(n : ℤ))
    have h₂ := Int.natCast_natAbs ((w.entry a-w.entry b)/(n : ℤ))
    rw [abs_of_nonneg hq] at h₁
    rw [abs_of_neg hq'] at h₂
    constructor <;> intro <;> omega

theorem ext_entry [NeZero n] {u v : AffinePermutation n} (h : u.entry=v.entry) : u=v := by
  have hp (i : Fin n) : (u.residue i,u.winding i)=(v.residue i,v.winding i) := by
    apply (AffinePermutation.integerIndex n).injective
    simpa only [AffinePermutation.integerIndex_apply,AffinePermutation.entry] using congrFun h i
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    exact congrArg Prod.fst (hp i)
  · funext i
    exact congrArg Prod.snd (hp i)

#print axioms inversion_swap_balance
#print axioms inversion_swap_lt_iff
end Guralnick.AffineAdjacentInversions
