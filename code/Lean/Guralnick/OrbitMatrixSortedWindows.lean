import Guralnick.OrbitLengthInput
import Guralnick.FiniteSource
import Mathlib.Data.List.Sort

/-! # Elementary uniqueness of a right-maximal window from its inverse winding -/
noncomputable section
namespace Guralnick.OrbitMatrixElementary
open Hecke CanonicalSchur
variable {N : ℕ} [NeZero N]

/-- Full finite right descents make the actual window strictly decreasing. -/
theorem right_maximal_strictAnti (c : WindowCoxeter N) (w : AffinePermutation N)
    (h : ∀ i ∈ (CanonicalChains.source (NeZero.pos N)).val,
      c.system.IsRightDescent w i) : StrictAnti w.entry := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  apply (c.finite_descent w i.castSucc i.succ (by simp)).mp
  apply h
  simp [CanonicalChains.source,CanonicalChains.omitNode]

/-- Equal inverse windings give exactly the same multiset of window entries. -/
theorem window_perm_of_inverse_winding {u v : AffinePermutation N}
    (h : (u⁻¹).winding = (v⁻¹).winding) : v.window.Perm u.window := by
  let σ : Equiv.Perm (Fin N) := v.residue.trans u.residue.symm
  have he : v.entry = u.entry ∘ σ := by
    funext i
    have hi := congrFun h (v.residue i)
    change -u.winding (u.residue.symm (v.residue i)) =
      -v.winding (v.residue.symm (v.residue i)) at hi
    rw [Equiv.symm_apply_apply] at hi
    have hw := neg_injective hi
    simp only [Function.comp_apply,AffinePermutation.entry,σ,Equiv.trans_apply,
      Equiv.apply_symm_apply,hw]
  unfold AffinePermutation.window
  rw [he]
  exact σ.ofFn_comp_perm u.entry

/-- No orbit-classification theorem is needed once the inverse winding is fixed. -/
theorem eq_of_right_maximal_inverse_winding (c : WindowCoxeter N)
    {u v : AffinePermutation N}
    (hu : ∀ i ∈ (CanonicalChains.source (NeZero.pos N)).val, c.system.IsRightDescent u i)
    (hv : ∀ i ∈ (CanonicalChains.source (NeZero.pos N)).val, c.system.IsRightDescent v i)
    (h : (u⁻¹).winding = (v⁻¹).winding) : u = v := by
  have he : v.window = u.window := List.eq_of_perm_of_sorted (r := (· ≥ ·))
    (window_perm_of_inverse_winding h)
    (right_maximal_strictAnti c v hv).antitone.ofFn_sorted
    (right_maximal_strictAnti c u hu).antitone.ofFn_sorted
  exact FiniteSource.affine_ext_entry (List.ofFn_injective he).symm

/-- One period of winding exceeds every possible difference of two residues. -/
theorem winding_le_of_entry_lt (w : AffinePermutation N) (i j : Fin N)
    (h : w.entry j < w.entry i) : w.winding j ≤ w.winding i := by
  have hi := (w.residue i).isLt
  have hj := (w.residue j).isLt
  have hN : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  unfold AffinePermutation.entry at h
  by_contra hn
  have hw : w.winding i+1 ≤ w.winding j := by omega
  have hm := mul_le_mul_of_nonneg_left hw (le_of_lt hN)
  push_cast at hi hj
  nlinarith

#print axioms eq_of_right_maximal_inverse_winding
end Guralnick.OrbitMatrixElementary
