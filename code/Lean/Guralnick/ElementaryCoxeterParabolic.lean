import Guralnick.ElementaryCoxeterFinite

/-!
# Finiteness and longest elements of proper affine parabolics

Deleting a cyclic node selects a length-n fundamental interval. A window
preserving that interval has winding determined by its residue permutation.
Every remaining simple reflection preserves the interval; hence every proper
parabolic embeds in a finite symmetric group. Its length function attains a
maximum, giving the required longest data without an external input.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterParabolic
open Hecke ParabolicWeb
open scoped BigOperators

/-- Which residues must be lifted once to lie above the omitted cut. -/
def cutPotential {n : ℕ} (a i : Fin n) : ℤ := if i.val<a.val then 1 else 0

def cutSubgroup {n : ℕ} (a : Fin n) : Subgroup (AffinePermutation n) where
  carrier := {w | ∀ i, w.winding i = cutPotential a (w.residue i)-cutPotential a i}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro u v hu hv i
    rw [AffinePermutation.mul_winding,hu,hv]
    simp only [AffinePermutation.mul_residue,Equiv.Perm.mul_apply]
    ring
  inv_mem' := by
    intro u hu i
    change -u.winding (u.residue.symm i) =
      cutPotential a (u.residue.symm i)-cutPotential a i
    rw [hu,u.residue.apply_symm_apply]
    ring

theorem cut_residue_injective {n : ℕ} (a : Fin n) :
    Function.Injective (fun w : cutSubgroup a => w.val.residue) := by
  intro u v h
  change u.val.residue=v.val.residue at h
  apply Subtype.ext
  apply AffinePermutation.ext h
  funext i
  rw [u.property,v.property,h]

instance cut_finite {n : ℕ} (a : Fin n) : Finite (cutSubgroup a) :=
  Finite.of_injective _ (cut_residue_injective a)

theorem simple_mem_cut (c : WindowCoxeter (n+1)) (a s : Fin (n+1)) (hsa : s≠a) :
    c.system.simple s ∈ cutSubgroup a := by
  classical
  by_cases hs : s=0
  · subst s
    have ha : 0<a.val := by have := a.isLt; exact Nat.pos_of_ne_zero (fun h => hsa (Fin.ext h.symm))
    have hna : ¬n<a.val := by have := a.isLt; omega
    intro i
    let σ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 (Fin.last n)
    have he : ((c.system.simple 0).residue i,(c.system.simple 0).winding i) =
        (σ i,cutPotential a (σ i)-cutPotential a i) := by
      apply (AffinePermutation.integerIndex (n+1)).injective
      rw [AffinePermutation.integerIndex_apply,AffinePermutation.integerIndex_apply]
      change (c.system.simple 0).entry i = _
      rw [c.simple_window]
      by_cases hi : i=0
      · subst i
        have hn : (0 : Fin (n+1))≠Fin.last n := by intro h; have := congrArg Fin.val h; simp at this; omega
        simp [σ,cutPotential,simpleEntry,ha,hn,hna]
        ring
      · by_cases hil : i=Fin.last n
        · subst i
          have hn : ¬n=0 := by omega
          simp [σ,cutPotential,simpleEntry,ha,hn,hna]
          ring
        · have hi0 : i.val≠0 := fun h => hi (Fin.ext h)
          have hil' : i.val≠n := fun h => hil (Fin.ext h)
          simp [σ,Equiv.swap_apply_of_ne_of_ne hi hil,cutPotential,simpleEntry,hi0,hil']
    have hr := congrArg Prod.fst he
    have hw := congrArg Prod.snd he
    dsimp only at hr hw
    rw [hr]
    exact hw
  · obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hs
    rw [FiniteSource.simple_eq_adjacent c j]
    intro i
    change 0 = cutPotential a ((Equiv.swap j.castSucc j.succ) i)-cutPotential a i
    have hja : j.val+1≠a.val := fun h => hsa (Fin.ext h)
    by_cases hi : i=j.castSucc
    · subst i
      simp only [Equiv.swap_apply_left,cutPotential,Fin.val_succ,Fin.coe_castSucc]
      split_ifs <;> omega
    · by_cases hi' : i=j.succ
      · subst i
        simp only [Equiv.swap_apply_right,cutPotential,Fin.val_succ,Fin.coe_castSucc]
        split_ifs <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hi hi',sub_self]

theorem subgroup_le_cut {n : ℕ} (c : WindowCoxeter n) (I : Index n)
    (a : Fin n) (ha : a ∉ I.val) : subgroup c I ≤ cutSubgroup a := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fin.pos a))
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨s,hs,rfl⟩
  exact simple_mem_cut c a s (fun h => ha (h ▸ hs))

theorem subgroup_finite {n : ℕ} (c : WindowCoxeter n) (I : Index n) :
    Finite (subgroup c I) := by
  classical
  have hex : ∃ a : Fin n, a ∉ I.val := by
    by_contra h
    apply I.property
    apply Finset.eq_univ_of_forall
    simpa using h
  obtain ⟨a,ha⟩ := hex
  let f : subgroup c I → cutSubgroup a := fun w => ⟨w.val,subgroup_le_cut c I a ha w.property⟩
  apply Finite.of_injective f
  intro u v h
  apply Subtype.ext
  exact congrArg (fun w : cutSubgroup a => w.val) h

/-- Longest data exists for every proper cyclic mask, by a proved finite
embedding and maximization of the actual Coxeter length. -/
def longestData {n : ℕ} (c : WindowCoxeter n) (I : Index n) : LongestData c I := by
  classical
  letI := subgroup_finite c I
  letI := Fintype.ofFinite (subgroup c I)
  let h := Finset.exists_max_image (Finset.univ : Finset (subgroup c I))
    (fun w => c.system.length w.val) Finset.univ_nonempty
  exact ⟨inferInstance,Classical.choose h,
    fun z => (Classical.choose_spec h).2 z (Finset.mem_univ z)⟩

#print axioms longestData

end Guralnick.ElementaryCoxeterParabolic
