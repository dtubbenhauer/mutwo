import Guralnick.LatticeFlagUnroll
import Guralnick.FiniteFlagExtension

/-! # Completing the actual subspace chain in a lattice period -/
noncomputable section
namespace Guralnick.LatticeFlagExtension
open LaurentLattice LatticeGallery LatticeFlags ElementaryCoxeterCutLength
variable {k : Type} [Field k] {n : ℕ} [NeZero n]
variable {S : Finset (Fin n)} (F : Flag k n S) (b : {i // i∈S})

def periodInterval : Submodule k (PeriodSpace F b) ≃o
    Set.Icc (F.node b).space (up (F.node b)).space :=
  quotientIntervalIso _ _ (le_up _)

def liftNode (W : Submodule k (PeriodSpace F b)) : Lattice k n :=
  intervalLattice (F.node b) (periodInterval F b W).val
    (periodInterval F b W).property.1 (periodInterval F b W).property.2

theorem liftNode_mono : Monotone (liftNode F b) := by
  intro W Z h
  exact (periodInterval F b).monotone h

@[simp] theorem liftNode_bot : liftNode F b ⊥=F.node b := by
  apply Lattice.space_injective
  apply le_antisymm
  · have h : periodInterval F b ⊥ ≤ ⟨(F.node b).space,le_rfl,le_up _⟩ :=
      by
        have h := (periodInterval F b).monotone
          (bot_le : ⊥ ≤ (periodInterval F b).symm ⟨(F.node b).space,le_rfl,le_up _⟩)
        simpa only [OrderIso.apply_symm_apply] using h
    exact h
  · exact (periodInterval F b ⊥).property.1

@[simp] theorem liftNode_top : liftNode F b ⊤=up (F.node b) := by
  apply Lattice.space_injective
  apply le_antisymm
  · exact (periodInterval F b ⊤).property.2
  · have h : (⟨(up (F.node b)).space,le_up _,le_rfl⟩ :
        Set.Icc (F.node b).space (up (F.node b)).space) ≤ periodInterval F b ⊤ :=
      by
        have h := (periodInterval F b).monotone
          (le_top : (periodInterval F b).symm ⟨(up (F.node b)).space,le_up _,le_rfl⟩ ≤ ⊤)
        simpa only [OrderIso.apply_symm_apply] using h
    exact h

@[simp] theorem liftNode_quotientNode (i : {i // i∈S}) :
    liftNode F b (quotientNode F b i)=raised F b i := by
  apply Lattice.space_injective
  exact congrArg Subtype.val ((periodInterval F b).apply_symm_apply
    ⟨(raised F b i).space,base_le_raised F b i,raised_le_up_base F b i⟩)

theorem liftNode_degree (W : Submodule k (PeriodSpace F b)) :
    degree k n (liftNode F b W)=(b.val.val : ℤ)+Module.finrank k W := by
  have hq : quotientImage (F.node b).space (up (F.node b)).space (le_up _)
      (liftNode F b W).space (periodInterval F b W).property.1
        (periodInterval F b W).property.2 = W :=
    (periodInterval F b).symm_apply_apply W
  have hr := quotientImage_finrank (F.node b).space (up (F.node b)).space (le_up _)
    (liftNode F b W).space (periodInterval F b W).property.1
      (periodInterval F b W).property.2
  rw [hq] at hr
  have hd := (congrArg (fun r : ℕ => (r : ℤ)) hr).trans
    (dimension_degree (F.node b) (liftNode F b W) (periodInterval F b W).property.1)
  rw [F.degree_eq b] at hd
  exact (eq_sub_iff_add_eq.mp hd).symm.trans (add_comm _ _)

/-- A full chain through the prescribed nodes of this one actual period. -/
structure FullPeriodChain where
  node : Fin (n+1) → Lattice k n
  ordered : Monotone node
  first : node ⟨0,by omega⟩=F.node b
  last : node (Fin.last n)=up (F.node b)
  degree_eq : ∀ i,degree k n (node i)=(b.val.val : ℤ)+i.val
  prescribed : ∀ i : {i // i∈S},
    node ⟨(cutRank b.val i.val).val,by have := (cutRank b.val i.val).isLt; omega⟩=raised F b i

/-- Actual finite-dimensional flag completion followed by the actual lattice
interval lift fills every missing node in one period. -/
theorem fullPeriodChain_nonempty : Nonempty (FullPeriodChain F b) := by
  classical
  let C : Finset (Submodule k (PeriodSpace F b)) :=
    insert ⊤ (Finset.univ.image (quotientNode F b))
  have htop : (⊤ : Submodule k (PeriodSpace F b))∈C := Finset.mem_insert_self _ _
  have hchain : ∀ A∈C,∀ B∈C,A ≤ B ∨ B ≤ A := by
    intro A hA B hB
    rcases Finset.mem_insert.mp hA with hA|hA
    · subst A; exact Or.inr le_top
    rcases Finset.mem_insert.mp hB with hB|hB
    · subst B; exact Or.inl le_top
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    rcases le_total (cutRank b.val i.val) (cutRank b.val j.val) with h|h
    · exact Or.inl (quotientNode_order F b i j h)
    · exact Or.inr (quotientNode_order F b j i h)
  obtain ⟨f,hmono,hrank,hpres⟩ := FiniteFlagExtension.exists_full_flag C htop hchain
  have hdim := periodSpace_finrank F b
  let q : Fin (n+1) → Submodule k (PeriodSpace F b) :=
    fun i => f ⟨i.val,by have := i.isLt; omega⟩
  have hqmono : Monotone q := by intro i j hij; exact hmono hij
  have hqrank (i : Fin (n+1)) : Module.finrank k (q i)=i.val := hrank _
  have hqzero : q ⟨0,by omega⟩=⊥ := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq bot_le
    rw [hqrank]
    simp
  have hqlast : q (Fin.last n)=⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [hqrank,finrank_top,hdim]
    rfl
  have hqpres (i : {i // i∈S}) :
      q ⟨(cutRank b.val i.val).val,by have := (cutRank b.val i.val).isLt; omega⟩=
        quotientNode F b i := by
    have hmem : quotientNode F b i∈C :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    have h := hpres _ hmem
    simpa only [q,quotientNode_rank] using h
  refine ⟨⟨fun i => liftNode F b (q i),(liftNode_mono F b).comp hqmono,?_,?_,?_,?_⟩⟩
  · dsimp only
    rw [hqzero,liftNode_bot]
  · dsimp only
    rw [hqlast,liftNode_top]
  · intro i
    rw [liftNode_degree,hqrank]
  · intro i
    dsimp only
    rw [hqpres,liftNode_quotientNode]

#print axioms fullPeriodChain_nonempty
end Guralnick.LatticeFlagExtension
