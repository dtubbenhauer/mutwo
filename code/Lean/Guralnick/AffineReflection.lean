import Guralnick.FiniteSource
import Guralnick.CanonicalSpherical

/-!
# Reflection of actual affine windows and ordinary canonical coefficients

The annular reflection reverses the residue order AND reverses winding.
Finite longest conjugation alone would have the wrong winding. The map
below is proved to be a group automorphism and to permute the Coxeter
simple generators. The general KL invariance under diagram automorphisms
is isolated as a literature input, quantified over every such automorphism.
-/

noncomputable section
namespace Guralnick.AffineReflection
open scoped BigOperators
open Hecke

/-- The order-reversing annular reflection preserves balanced periodicity. -/
def reflect {n : ℕ} (w : AffinePermutation n) : AffinePermutation n where
  residue := Fin.revPerm*w.residue*Fin.revPerm
  winding i := -w.winding i.rev
  balanced := by
    rw [Finset.sum_neg_distrib]
    have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) w.winding
    simpa only [Fin.revPerm_apply, w.balanced, neg_eq_zero] using h

@[simp] theorem reflect_residue {n : ℕ} (w : AffinePermutation n) (i : Fin n) :
    (reflect w).residue i = (w.residue i.rev).rev := rfl

@[simp] theorem reflect_winding {n : ℕ} (w : AffinePermutation n) (i : Fin n) :
    (reflect w).winding i = -w.winding i.rev := rfl

@[simp] theorem reflect_reflect {n : ℕ} (w : AffinePermutation n) : reflect (reflect w)=w := by
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    simp
  · funext i
    simp

theorem reflect_mul {n : ℕ} (u v : AffinePermutation n) :
    reflect (u*v)=reflect u*reflect v := by
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    simp only [reflect_residue, AffinePermutation.mul_residue, Equiv.Perm.mul_apply,
      Fin.rev_rev]
  · funext i
    simp only [reflect_winding, AffinePermutation.mul_winding, reflect_residue,
      Fin.rev_rev, neg_add_rev]
    ring

def equiv (n : ℕ) : AffinePermutation n ≃* AffinePermutation n where
  toEquiv := Function.Involutive.toPerm reflect reflect_reflect
  map_mul' := reflect_mul

theorem reflect_entry {n : ℕ} (w : AffinePermutation n) (i : Fin n) :
    (reflect w).entry i=(n : ℤ)+1-w.entry i.rev := by
  have h := (w.residue i.rev).isLt
  simp only [AffinePermutation.entry, reflect_residue, reflect_winding, Fin.val_rev,
    Nat.cast_sub (show (w.residue i.rev).val+1≤n by omega), Nat.cast_add,
    Nat.cast_one, mul_neg]
  ring

def node {n : ℕ} (s : Fin n) : Fin n :=
  ⟨if s.val=0 then 0 else n-s.val, by have hs:=s.isLt; split_ifs <;> omega⟩

@[simp] theorem node_node {n : ℕ} (s : Fin n) : node (node s)=s := by
  apply Fin.ext
  have hs:=s.isLt
  simp only [node]
  split_ifs <;> omega

def nodeEquiv (n : ℕ) : Equiv.Perm (Fin n) := Function.Involutive.toPerm node node_node

theorem simpleEntry_reflect {n : ℕ} (hn : 2≤n) (s i : Fin n) :
    (n : ℤ)+1-simpleEntry s i.rev = simpleEntry (node s) i := by
  have hs:=s.isLt
  have hi:=i.isLt
  unfold simpleEntry
  simp only [Fin.val_rev, node]
  by_cases hz : s.val=0
  · simp only [hz, if_true]
    split_ifs <;> push_cast <;> omega
  · have hnz : ¬n-s.val=0 := by omega
    simp only [hz, if_false, hnz]
    have he : i.rev=s ↔ n-(i.val+1)=s.val := by exact Fin.ext_iff
    simp only [he]
    have he' : i=⟨n-s.val, by omega⟩ ↔ i.val=n-s.val := by exact Fin.ext_iff
    simp only [he']
    split_ifs <;> push_cast <;> omega

theorem reflect_simple {n : ℕ} [NeZero n] (hn : 2≤n) (c : WindowCoxeter n) (s : Fin n) :
    reflect (c.system.simple s)=c.system.simple (node s) := by
  apply FiniteSource.affine_ext_entry
  funext i
  rw [reflect_entry, c.simple_window, c.simple_window, simpleEntry_reflect hn]

@[simp] theorem reflect_inv {n : ℕ} (w : AffinePermutation n) :
    reflect w⁻¹=(reflect w)⁻¹ := (equiv n).map_inv w

theorem reflect_wordProd {n : ℕ} [NeZero n] (hn : 2≤n) (c : WindowCoxeter n)
    (l : List (Fin n)) : reflect (c.system.wordProd l)=c.system.wordProd (l.map node) := by
  induction l with
  | nil => exact (equiv n).map_one
  | cons i l ih =>
    rw [List.map_cons, c.system.wordProd_cons, c.system.wordProd_cons,
      reflect_mul, reflect_simple hn c, ih]

theorem length_reflect {n : ℕ} [NeZero n] (hn : 2≤n) (c : WindowCoxeter n)
    (w : AffinePermutation n) : c.system.length (reflect w)=c.system.length w := by
  have hle (z : AffinePermutation n) : c.system.length (reflect z)≤c.system.length z := by
    obtain ⟨l, hl, rfl⟩:=c.system.exists_reduced_word z
    rw [reflect_wordProd hn c]
    exact (c.system.length_wordProd_le (l.map node)).trans (by simp [hl])
  exact le_antisymm (hle w) (by simpa using hle (reflect w))

theorem left_descent_reflect {n : ℕ} [NeZero n] (hn : 2≤n) (c : WindowCoxeter n)
    (w : AffinePermutation n) (i : Fin n) :
    c.system.IsLeftDescent (reflect w) (node i) ↔ c.system.IsLeftDescent w i := by
  unfold CoxeterSystem.IsLeftDescent
  rw [←reflect_simple hn c, ←reflect_mul, length_reflect hn c, length_reflect hn c]

theorem right_descent_reflect {n : ℕ} [NeZero n] (hn : 2≤n) (c : WindowCoxeter n)
    (w : AffinePermutation n) (i : Fin n) :
    c.system.IsRightDescent (reflect w) (node i) ↔ c.system.IsRightDescent w i := by
  unfold CoxeterSystem.IsRightDescent
  rw [←reflect_simple hn c, ←reflect_mul, length_reflect hn c, length_reflect hn c]

/-- General ordinary KL invariance under Coxeter diagram automorphisms,
a consequence of the uniqueness of the bar-invariant triangular basis.
There are no assumptions about the manuscript's particular indices here. -/
def DiagramInvarianceInput {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c) : Prop :=
  ∀ (e : AffinePermutation n ≃* AffinePermutation n) (σ : Equiv.Perm (Fin n)),
    (∀ i, e (c.system.simple i)=c.system.simple (σ i)) →
    ∀ y w, K.standard.repr (K.canonical (e w)) (e y) =
      K.standard.repr (K.canonical w) y

theorem canonical_reflection {n : ℕ} [NeZero n] {c : WindowCoxeter n}
    (hn : 2≤n) (K : KLRealization c) (h : DiagramInvarianceInput K) (y w : AffinePermutation n) :
    K.standard.repr (K.canonical (reflect w)) (reflect y) =
      K.standard.repr (K.canonical w) y :=
  h (equiv n) (nodeEquiv n) (reflect_simple hn c) y w

@[simp] theorem reflect_longest (n : ℕ) :
    reflect (AffinePermutation.longest n)=AffinePermutation.longest n := by
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    simp
  · funext i
    simp

theorem smallResidue_rev (m j : ℕ) (i : Fin (2*m+1)) :
    Weights.smallResidue m j i.rev = -Weights.smallResidue m j i := by
  have hi:=i.isLt
  simp only [Weights.smallResidue, Fin.val_rev, Nat.add_sub_add_right]
  by_cases h : i.val<m
  · have h₁ : ¬2*m-i.val<m := by omega
    have h₂ : ¬2*m-i.val=m := by omega
    have h₃ : 2*m-(2*m-i.val)=i.val := by omega
    simp [h, h₁, h₂, h₃]
  · by_cases he : i.val=m
    · have hm : 2*m-m=m := by omega
      simp [he, hm]
    · have h₁ : 2*m-i.val<m := by omega
      simp [h, he, h₁]

@[simp] theorem reflect_family {m j : ℕ} (hm : 2≤m) (hj : 1≤j) (hjm : j≤m) :
    reflect (Family.affine hm hj hjm)=Family.affine hm hj hjm := by
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    apply Fin.ext
    have h₁ := Family.residue_value hm hj hjm i
    have h₂ := Family.residue_value hm hj hjm i.rev
    rw [smallResidue_rev] at h₂
    change (((Family.residue hm hj hjm i.rev).rev).val)=
      (Family.residue hm hj hjm i).val
    simp only [Fin.val_rev]
    have hbound := (Family.residue hm hj hjm i.rev).isLt
    omega
  · funext i
    simp only [reflect_winding]
    change -Family.winding m j i.rev=Family.winding m j i
    rw [Family.winding_rev hjm, neg_neg]

@[simp] theorem reflect_upper {m j : ℕ} (hm : 2≤m) (hj : 1≤j) (hjm : j≤m) :
    reflect (Family.upper hm hj hjm)=Family.upper hm hj hjm := by
  simp [Family.upper, reflect_mul]

@[simp] theorem reflect_spherical (m r : ℕ) :
    reflect (CanonicalSpherical.index m r)=CanonicalSpherical.index m r := by
  unfold CanonicalSpherical.index
  rw [reflect_mul, reflect_longest]
  congr 1
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    simp [CanonicalSpherical.translation]
  · funext i
    simp only [reflect_winding, CanonicalSpherical.translation]
    rw [Family.winding_rev (Nat.min_le_right r m), neg_neg]

end Guralnick.AffineReflection
