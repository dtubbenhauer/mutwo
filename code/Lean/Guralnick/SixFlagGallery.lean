import Guralnick.LatticeFlags

/-!
# The six retained-mask galleries and their incidence conditions

These declarations use genuine full Laurent-series lattices. The six
compatibility relations use exactly the masks of the parabolic web.
-/
noncomputable section
namespace Guralnick.LatticeFlags.Family
open LaurentLattice
variable {k : Type*} [Field k] {m : ℕ}

abbrev S (m : ℕ) := retained (ParabolicWeb.Family.source m)
abbrev O (m : ℕ) := retained (ParabolicWeb.Family.output m)
abbrev J (m : ℕ) := retained (ParabolicWeb.Family.cyclic m)
abbrev C (m : ℕ) := retained (ParabolicWeb.Family.common m)
abbrev M (m : ℕ) := retained (ParabolicWeb.Family.middle m)

structure SixGallery (source : Flag k (2*m+1) (S m))
    (target : Flag k (2*m+1) (O m)) where
  first : Flag k (2*m+1) (O m)
  cyclic : Flag k (2*m+1) (J m)
  firstCommon : Flag k (2*m+1) (C m)
  middle : Flag k (2*m+1) (M m)
  secondCommon : Flag k (2*m+1) (C m)
  step1 : Compatible source first
  step2 : Compatible first cyclic
  step3 : Compatible cyclic firstCommon
  step4 : Compatible firstCommon middle
  step5 : Compatible middle secondCommon
  step6 : Compatible secondCommon target

@[ext] theorem SixGallery.ext {source : Flag k (2*m+1) (S m)}
    {target : Flag k (2*m+1) (O m)} {g h : SixGallery source target}
    (h1 : g.first = h.first) (h2 : g.cyclic = h.cyclic)
    (h3 : g.firstCommon = h.firstCommon) (h4 : g.middle = h.middle)
    (h5 : g.secondCommon = h.secondCommon) : g = h := by
  cases g; cases h; cases h1; cases h2; cases h3; cases h4; cases h5; rfl

def SixGallery.toGallery {source : Flag k (2*m+1) (S m)}
    {target : Flag k (2*m+1) (O m)} (g : SixGallery source target) :
    Gallery (masks m) source target where
  flags := Fin.cases source (Fin.cases g.first (Fin.cases g.cyclic
    (Fin.cases g.firstCommon (Fin.cases g.middle (Fin.cases g.secondCommon
      (Fin.cases target (fun i => Fin.elim0 i)))))))
  source_eq := rfl
  target_eq := rfl
  adjacent i := by
    fin_cases i
    · exact g.step1
    · exact g.step2
    · exact g.step3
    · exact g.step4
    · exact g.step5
    · exact g.step6

def SixGallery.ofGallery {source : Flag k (2*m+1) (S m)}
    {target : Flag k (2*m+1) (O m)} (g : Gallery (masks m) source target) :
    SixGallery source target where
  first := g.flags 1
  cyclic := g.flags 2
  firstCommon := g.flags 3
  middle := g.flags 4
  secondCommon := g.flags 5
  step1 := by
    have h : Compatible (g.flags 0) (g.flags 1) := g.adjacent 0
    simpa only [g.source_eq] using h
  step2 := g.adjacent 1
  step3 := g.adjacent 2
  step4 := g.adjacent 3
  step5 := g.adjacent 4
  step6 := by
    have h : Compatible (g.flags 5) (g.flags (Fin.last 6)) := g.adjacent 5
    simpa only [g.target_eq] using h

/-- The explicit six stages are exactly the generic gallery for the seven
retained masks, with no additional refinements. -/
def sixGalleryEquiv {source : Flag k (2*m+1) (S m)}
    {target : Flag k (2*m+1) (O m)} :
    SixGallery source target ≃ Gallery (masks m) source target where
  toFun := SixGallery.toGallery
  invFun := SixGallery.ofGallery
  left_inv g := by cases g; rfl
  right_inv g := by
    apply Gallery.ext
    funext i
    fin_cases i
    · exact g.source_eq.symm
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact g.target_eq.symm

def atNode {N : ℕ} {mask : Finset (Fin N)} (F : Flag k N mask)
    (i : ℕ) (hi : i < N) (hm : (⟨i,hi⟩ : Fin N) ∈ mask) : Lattice k N :=
  F.node ⟨⟨i,hi⟩,hm⟩

def sourceNode (source : Flag k (2*m+1) (S m)) : Lattice k (2*m+1) :=
  atNode source 0 (by omega) ((source_mem m _).mpr rfl)

def targetNode (target : Flag k (2*m+1) (O m)) : Lattice k (2*m+1) :=
  atNode target 0 (by omega) ((output_mem m _).mpr (Or.inl rfl))

def targetF (target : Flag k (2*m+1) (O m)) : Lattice k (2*m+1) :=
  atNode target m (by omega) ((output_mem m _).mpr (Or.inr (Or.inl rfl)))

def targetF' (hm : 2 ≤ m) (target : Flag k (2*m+1) (O m)) : Lattice k (2*m+1) :=
  atNode target (m+1) (by omega) ((output_mem m _).mpr (Or.inr (Or.inr rfl)))

variable (hm : 2 ≤ m) {source : Flag k (2*m+1) (S m)}
  {target : Flag k (2*m+1) (O m)} (g : SixGallery source target)

def I : Lattice k (2*m+1) :=
  atNode g.first m (by omega) ((output_mem m _).mpr (Or.inr (Or.inl rfl)))
def K : Lattice k (2*m+1) :=
  atNode g.first (m+1) (by omega) ((output_mem m _).mpr (Or.inr (Or.inr rfl)))
def L : Lattice k (2*m+1) :=
  atNode g.firstCommon 1 (by omega) ((common_mem m _).mpr (Or.inr (Or.inl rfl)))
def H : Lattice k (2*m+1) :=
  atNode g.firstCommon (2*m) (by omega)
    ((common_mem m _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem first_common (i : ℕ) (hi : i=m ∨ i=m+1) :
    atNode g.first i (by omega) ((output_mem m _).mpr (Or.inr hi)) =
      atNode g.firstCommon i (by omega) ((common_mem m _).mpr (by tauto)) := by
  exact (g.step2 ⟨i,by omega⟩ _ ((cyclic_mem m _).mpr hi)).trans
    (g.step3 ⟨i,by omega⟩ ((cyclic_mem m _).mpr hi) _)

theorem common_common (i : ℕ) (hi : i=0 ∨ i=1 ∨ i=2*m) :
    atNode g.firstCommon i (by omega) ((common_mem m _).mpr (by tauto)) =
      atNode g.secondCommon i (by omega) ((common_mem m _).mpr (by tauto)) := by
  exact (g.step4 ⟨i,by omega⟩ _ ((middle_mem m _).mpr hi)).trans
    (g.step5 ⟨i,by omega⟩ ((middle_mem m _).mpr hi) _)

theorem common_zero :
    atNode g.firstCommon 0 (by omega) ((common_mem m _).mpr (Or.inl rfl)) =
      targetNode target := by
  exact (common_common hm g 0 (Or.inl rfl)).trans (g.step6 ⟨0,by omega⟩ _ _)

/-- Extract the actual ambient incidence gallery from the six flag maps.
In particular, support is derived from refinement compatibility. -/
def toIncidence : LatticeGallery.Incidence (shift k (2*m+1))
    (sourceNode source).space (targetNode target).space
    (targetF target).space (targetF' hm target).space := by
  have hsource : sourceNode source =
      atNode g.first 0 (by omega) ((output_mem m _).mpr (Or.inl rfl)) :=
    g.step1 ⟨0,by omega⟩ _ _
  have hI := first_common hm g m (Or.inl rfl)
  have hK := first_common hm g (m+1) (Or.inr rfl)
  have hzero := common_zero hm g
  have hL := common_common hm g 1 (Or.inr (Or.inl rfl))
  have hH := common_common hm g (2*m) (Or.inr (Or.inr rfl))
  have hF := g.step6 ⟨m,by omega⟩
    ((common_mem m _).mpr (Or.inr (Or.inr (Or.inl rfl))))
    ((output_mem m _).mpr (Or.inr (Or.inl rfl)))
  have hF' := g.step6 ⟨m+1,by omega⟩
    ((common_mem m _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    ((output_mem m _).mpr (Or.inr (Or.inr rfl)))
  refine {
    L := (L hm g).space
    I := (I hm g).space
    K := (K hm g).space
    H := (H g).space
    source_le_I := ?_
    I_le_K := ?_
    K_le_source_expand := ?_
    target_le_L := ?_
    L_le_I := ?_
    K_le_H := ?_
    H_le_target_expand := ?_
    L_le_F := ?_
    F'_le_H := ?_ }
  · rw [hsource]
    exact g.first.ordered _ _ (by simp only [Fin.le_def]; omega)
  · exact g.first.ordered _ _ (by simp only [Fin.le_def]; omega)
  · rw [hsource]
    exact g.first.cyclic _ _
  · rw [← hzero]
    exact g.firstCommon.ordered _ _ (by simp only [Fin.le_def]; omega)
  · change (L hm g).space ≤ (atNode g.first m _ _).space
    rw [hI]
    exact g.firstCommon.ordered _ _ (by simp only [Fin.le_def]; omega)
  · change (atNode g.first (m+1) _ _).space ≤ (H g).space
    rw [hK]
    exact g.firstCommon.ordered _ _ (by simp only [Fin.le_def]; omega)
  · rw [← hzero]
    exact g.firstCommon.cyclic _ _
  · change (atNode g.firstCommon 1 _ _).space ≤ _
    rw [hL]
    change _ ≤ (target.node ⟨⟨m,by omega⟩,_⟩).space
    rw [← hF]
    exact g.secondCommon.ordered _ _ (by simp only [Fin.le_def]; omega)
  · change (target.node ⟨⟨m+1,by omega⟩,_⟩).space ≤ (atNode g.firstCommon (2*m) _ _).space
    rw [hH, ← hF']
    exact g.secondCommon.ordered _ _ (by simp only [Fin.le_def]; omega)

include hm g in
/-- Both one-step endpoint bounds are consequences of the actual six-mask
flag gallery, before any relative-matrix or counting theorem is used. -/
theorem endpoint_bounds :
    (sourceNode source).space ≤ LatticeGallery.expand (shift k (2*m+1))
      (targetNode target).space ∧
    (targetNode target).space ≤ LatticeGallery.expand (shift k (2*m+1))
      (sourceNode source).space :=
  LatticeGallery.endpoint_bounds (toIncidence hm g)

end Guralnick.LatticeFlags.Family
