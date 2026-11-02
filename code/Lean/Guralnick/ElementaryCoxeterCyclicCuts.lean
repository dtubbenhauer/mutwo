import Guralnick.ElementaryCoxeterRotation
import Guralnick.ElementaryCoxeterPackets

/-! # Positive list boundaries and the actual cyclic omitted nodes -/
noncomputable section
namespace Guralnick.ElementaryCoxeterCyclicCuts
open Hecke ParabolicWeb ElementaryCoxeterParabolic ElementaryCoxeterCutLength
open ElementaryCoxeterRotation ElementaryCoxeterPackets

theorem cutRank_shift {n : ℕ} (a : Fin n) (r : ℕ) :
    cutEquiv a (⟨(a.val+r)%n,Nat.mod_lt _ (Fin.pos a)⟩ : Fin n)=
      ⟨r%n,Nat.mod_lt _ (Fin.pos a)⟩ := by
  apply Fin.ext
  change (if (a.val+r)%n<a.val then (a.val+r)%n+n-a.val else (a.val+r)%n-a.val)=r%n
  have ha:=a.isLt
  have hr:=Nat.mod_lt r (Fin.pos a)
  have h := Nat.add_mod_add_ite a.val r n
  rw [Nat.mod_eq_of_lt ha] at h
  split_ifs at h <;> split_ifs <;> omega

theorem mem_cuts_iff {n : ℕ} (A : FiniteBlocks.Composition n) (s : Fin n) :
    s ∈ A.cuts ↔ ∃ r ∈ A.packets.scanl (·+·) 0,
      (cutEquiv A.cut s).val=r%n := by
  classical
  have hscan := scanl_add A.packets A.cut.val 0
  simp only [Nat.add_zero] at hscan
  unfold FiniteBlocks.Composition.cuts
  rw [hscan,List.map_map]
  simp only [List.mem_toFinset,List.mem_map,Function.comp_apply]
  constructor
  · rintro ⟨r,hr,hs⟩
    refine ⟨r,hr,?_⟩
    have h := congrArg (fun i => (cutEquiv A.cut i).val) hs
    dsimp only at h
    rw [cutRank_shift] at h
    exact h.symm
  · rintro ⟨r,hr,hs⟩
    refine ⟨r,hr,?_⟩
    apply (cutEquiv A.cut).injective
    apply Fin.ext
    rw [cutRank_shift]
    exact hs.symm

theorem positive_mem_cuts_iff {n : ℕ} (A : FiniteBlocks.Composition n)
    (z : Fin n) (hz : 0<z.val) :
    (cutEquiv A.cut).symm z ∈ A.cuts ↔ z.val ∈ A.packets.scanl (·+·) 0 := by
  rw [mem_cuts_iff]
  simp only [Equiv.apply_symm_apply]
  constructor
  · rintro ⟨r,hr,he⟩
    have hrn : r≤n := by simpa only [A.total] using scanl_le_sum A.packets hr
    have hrlt : r<n := by
      by_contra h
      have hEq : r=n := by omega
      simp [hEq] at he
      omega
    rw [Nat.mod_eq_of_lt hrlt] at he
    simpa only [he] using hr
  · intro hz
    exact ⟨z.val,hz,(Nat.mod_eq_of_lt z.isLt).symm⟩

/-- The input mask consists exactly of the nonboundary adjacent edges
in the linearly ordered packet partition. -/
theorem positive_mem_index_iff {n : ℕ} (A : FiniteBlocks.Composition n)
    (z : Fin n) (hz : 0<z.val) :
    (cutEquiv A.cut).symm z ∈ A.index.val ↔ z.val ∉ A.packets.scanl (·+·) 0 := by
  change _ ∈ A.cutsᶜ ↔ _
  rw [Finset.mem_compl,positive_mem_cuts_iff A z hz]

#print axioms positive_mem_index_iff
end Guralnick.ElementaryCoxeterCyclicCuts
