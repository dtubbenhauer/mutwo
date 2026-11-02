import Guralnick.FiniteBlocks
import Guralnick.FiniteSource
import Mathlib.Order.Fin.Basic

/-!
# The finite-parabolic longest element is literal reversal

A longest element has every generating right descent. The standard finite
parabolic has zero winding, so the descent criterion makes its residue
permutation strictly decreasing. A decreasing permutation of a finite
chain is reversal. No longest-element identification is assumed.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterFinite
open Hecke ParabolicWeb

variable {n : ℕ} (c : WindowCoxeter n)

theorem longest_right_descent (I : Index n) (D : LongestData c I)
    (i : Fin n) (hi : i ∈ I.val) : c.system.IsRightDescent D.longest.val i := by
  have hs : c.system.simple i ∈ subgroup c I := Subgroup.subset_closure ⟨i,hi,rfl⟩
  have hmax := D.length_max (D.longest*⟨c.system.simple i,hs⟩)
  change c.system.length (D.longest.val*c.system.simple i) ≤ c.system.length D.longest.val at hmax
  exact lt_of_le_of_ne hmax (c.system.length_mul_simple_ne _ _)

theorem source_le_finite (c : WindowCoxeter (n+1)) :
    subgroup c (CanonicalChains.source (Nat.succ_pos n)) ≤
      (AffinePermutation.finiteEmbedding (n+1)).range := by
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨i,hi,rfl⟩
  have hi0 : i ≠ 0 := by
    simpa [CanonicalChains.source,CanonicalChains.omitNode] using hi
  obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
  exact ⟨Equiv.swap j.castSucc j.succ,FiniteSource.simple_eq_adjacent c j |>.symm⟩

theorem decreasing_permutation (σ : Equiv.Perm (Fin n)) (h : StrictAnti σ) :
    σ=Fin.revPerm := by
  let e : Equiv.Perm (Fin n) := Fin.revPerm*σ
  have he : StrictMono e := Fin.rev_strictAnti.comp h
  let f := he.orderIsoOfRightInverse e e.symm e.apply_symm_apply
  apply Equiv.ext
  intro i
  have hi := Fin.coe_orderIso_apply f i
  have heq : (σ i).rev=i := Fin.ext hi
  simpa using congrArg Fin.rev heq

theorem standardFiniteLongest (D : ∀ I : Index n, LongestData c I) :
    FiniteBlocks.StandardFiniteLongestInput D := by
  intro hn
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let I := CanonicalChains.source hn
  obtain ⟨σ,hσ⟩ := source_le_finite c (D I).longest.property
  have hanti : StrictAnti σ := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro a
    have hi : a.succ ∈ I.val := by
      simp [I,CanonicalChains.source,CanonicalChains.omitNode]
    have hd := longest_right_descent c I (D I) a.succ hi
    rw [c.finite_descent _ a.castSucc a.succ (by simp),←hσ] at hd
    simpa [AffinePermutation.entry,AffinePermutation.finiteEmbedding] using hd
  rw [←hσ,decreasing_permutation σ hanti]
  rfl

#print axioms standardFiniteLongest
end Guralnick.ElementaryCoxeterFinite
