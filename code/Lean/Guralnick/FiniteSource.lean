import Guralnick.ParabolicWeb
import Mathlib.GroupTheory.Perm.Sign

/-!
# The actual finite symmetric subgroup

The finite parabolic omitting the affine generator contains every
zero-winding finite permutation. This is proved using mathlib's adjacent
transposition generation theorem and the explicit simple windows.
-/

namespace Guralnick.FiniteSource
open Hecke ParabolicWeb

theorem affine_ext_entry {n : ℕ} [NeZero n] {u v : AffinePermutation n}
    (h : u.entry = v.entry) : u = v := by
  have hp (i : Fin n) : (u.residue i, u.winding i) = (v.residue i, v.winding i) := by
    apply (AffinePermutation.integerIndex n).injective
    simpa only [AffinePermutation.integerIndex_apply, AffinePermutation.entry] using congrFun h i
  apply AffinePermutation.ext
  · apply Equiv.ext
    intro i
    exact congrArg Prod.fst (hp i)
  · funext i
    exact congrArg Prod.snd (hp i)

theorem simple_eq_adjacent {n : ℕ} (c : WindowCoxeter (n+1)) (i : Fin n) :
    c.system.simple i.succ =
      AffinePermutation.finiteEmbedding (n+1) (Equiv.swap i.castSucc i.succ) := by
  apply affine_ext_entry
  funext a
  rw [c.simple_window]
  simp only [simpleEntry, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    if_false, AffinePermutation.entry, AffinePermutation.finiteEmbedding,
    Pi.zero_apply, mul_zero, add_zero]
  by_cases h : a=i.castSucc
  · subst a
    simp
  · by_cases h' : a=i.succ
    · subst a
      simp
    · have hn : ¬a.val+1=i.val+1 := by
        intro ha
        exact h (Fin.ext (by simpa using ha))
      have hv : a.val ≠ i.val := fun ha => h (Fin.ext ha)
      simp [h, h', hv, Equiv.swap_apply_of_ne_of_ne]

theorem finiteEmbedding_mem_source (m : ℕ) (c : WindowCoxeter (2*m+1))
    (σ : Equiv.Perm (Fin (2*m+1))) :
    AffinePermutation.finiteEmbedding (2*m+1) σ ∈ subgroup c (Family.source m) := by
  let S := subgroup c (Family.source m)
  let M := S.toSubmonoid.comap (AffinePermutation.finiteEmbedding (2*m+1))
  have htop : Submonoid.closure
      (Set.range fun i : Fin (2*m) => Equiv.swap i.castSucc i.succ) ≤ M := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    change AffinePermutation.finiteEmbedding (2*m+1)
      (Equiv.swap i.castSucc i.succ) ∈ S
    rw [←simple_eq_adjacent c i]
    apply Subgroup.subset_closure
    refine ⟨i.succ, ?_, rfl⟩
    simp [Family.source, Family.sourceSet]
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at htop
  exact htop (Submonoid.mem_top σ)

end Guralnick.FiniteSource
