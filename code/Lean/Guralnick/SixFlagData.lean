import Guralnick.SixFlagGallery
import Guralnick.FlagConstructors
import Guralnick.LatticeTheory

noncomputable section
namespace Guralnick.LatticeFlags.Family
open LaurentLattice
variable {k : Type*} [Field k] {m : ℕ} (hm : 2 ≤ m)
  (source : Flag k (2*m+1) (S m)) (target : Flag k (2*m+1) (O m))

/-- The four actual lattice choices, their incidence conditions and their
absolute degrees. No unproved dimension or counting interpretation is
hidden in this type. -/
structure Data where
  L : Lattice k (2*m+1)
  I : Lattice k (2*m+1)
  K : Lattice k (2*m+1)
  H : Lattice k (2*m+1)
  source_le_I : sourceNode source ≤ I
  I_le_K : I ≤ K
  K_le_source_expand : K.space ≤ LatticeGallery.expand (shift k (2*m+1))
    (sourceNode source).space
  target_le_L : targetNode target ≤ L
  L_le_I : L ≤ I
  K_le_H : K ≤ H
  H_le_target_expand : H.space ≤ LatticeGallery.expand (shift k (2*m+1))
    (targetNode target).space
  L_le_F : L ≤ targetF target
  F'_le_H : targetF' hm target ≤ H
  degree_L : degree k (2*m+1) L = 1
  degree_I : degree k (2*m+1) I = m
  degree_K : degree k (2*m+1) K = m+1
  degree_H : degree k (2*m+1) H = 2*m

@[ext] theorem Data.ext {d e : Data hm source target}
    (hL : d.L=e.L) (hI : d.I=e.I) (hK : d.K=e.K) (hH : d.H=e.H) : d=e := by
  cases d; cases e; cases hL; cases hI; cases hK; cases hH; rfl

variable {source target}

def Data.toIncidence (d : Data hm source target) :
    LatticeGallery.Incidence (shift k (2*m+1)) (sourceNode source).space
      (targetNode target).space (targetF target).space (targetF' hm target).space where
  L := d.L.space
  I := d.I.space
  K := d.K.space
  H := d.H.space
  source_le_I := d.source_le_I
  I_le_K := d.I_le_K
  K_le_source_expand := d.K_le_source_expand
  target_le_L := d.target_le_L
  L_le_I := d.L_le_I
  K_le_H := d.K_le_H
  H_le_target_expand := d.H_le_target_expand
  L_le_F := d.L_le_F
  F'_le_H := d.F'_le_H

def SixGallery.toData (g : SixGallery source target) : Data hm source target where
  L := Family.L hm g
  I := Family.I hm g
  K := Family.K hm g
  H := Family.H g
  source_le_I := (toIncidence hm g).source_le_I
  I_le_K := (toIncidence hm g).I_le_K
  K_le_source_expand := (toIncidence hm g).K_le_source_expand
  target_le_L := (toIncidence hm g).target_le_L
  L_le_I := (toIncidence hm g).L_le_I
  K_le_H := (toIncidence hm g).K_le_H
  H_le_target_expand := (toIncidence hm g).H_le_target_expand
  L_le_F := (toIncidence hm g).L_le_F
  F'_le_H := (toIncidence hm g).F'_le_H
  degree_L := g.firstCommon.degree_eq _
  degree_I := g.first.degree_eq _
  degree_K := by
    simpa using (g.first.degree_eq
      ⟨⟨m+1,by omega⟩,(output_mem m _).mpr (Or.inr (Or.inr rfl))⟩)
  degree_H := by
    simpa using (g.firstCommon.degree_eq
      ⟨⟨2*m,by omega⟩,(common_mem m _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩)

private theorem J_sub_O : J m ⊆ O m := by
  intro i hi
  exact (output_mem m i).mpr (Or.inr ((cyclic_mem m i).mp hi))

private theorem M_sub_C : M m ⊆ C m := by
  intro i hi
  have h := (middle_mem m i).mp hi
  apply (common_mem m i).mpr
  tauto

def Data.firstFlag (d : Data hm source target) : Flag k (2*m+1) (O m) :=
  three hm (sourceNode source) d.I d.K d.source_le_I d.I_le_K
    d.K_le_source_expand (source.degree_eq _) d.degree_I d.degree_K

def Data.firstCommonFlag (d : Data hm source target) : Flag k (2*m+1) (C m) :=
  five hm (targetNode target) d.L d.I d.K d.H d.target_le_L d.L_le_I
    d.I_le_K d.K_le_H d.H_le_target_expand (target.degree_eq _)
    d.degree_L d.degree_I d.degree_K d.degree_H

def Data.secondCommonFlag (d : Data hm source target) : Flag k (2*m+1) (C m) :=
  five hm (targetNode target) d.L (targetF target) (targetF' hm target) d.H
    d.target_le_L d.L_le_F (target.ordered _ _ (by simp only [Fin.le_def]; omega))
    d.F'_le_H d.H_le_target_expand (target.degree_eq _) d.degree_L
    (target.degree_eq _) (by simpa using (target.degree_eq
      ⟨⟨m+1,by omega⟩,(output_mem m _).mpr (Or.inr (Or.inr rfl))⟩)) d.degree_H

/-- Reconstruct every intermediate partial flag from the four lattice
choices. The common facets introduce no further choices. -/
def Data.toSixGallery (d : Data hm source target) : SixGallery source target where
  first := d.firstFlag hm
  cyclic := (d.firstFlag hm).restrict J_sub_O
  firstCommon := d.firstCommonFlag hm
  middle := (d.firstCommonFlag hm).restrict M_sub_C
  secondCommon := d.secondCommonFlag hm
  step1 := by
    rintro ⟨i,hi⟩ hs ht
    have hh := (source_mem m ⟨i,hi⟩).mp hs
    change i = 0 at hh
    subst i
    rfl
  step2 := compatible_restrict _ _
  step3 := by
    rintro ⟨i,hi⟩ hJ hC
    have hh := (cyclic_mem m ⟨i,hi⟩).mp hJ
    change i=m ∨ i=m+1 at hh
    rcases hh with hh | hh <;> subst i
    all_goals simp only [Flag.restrict, Data.firstFlag, Data.firstCommonFlag,
      three, five, ofBounds, threeNodes, fiveNodes]
    all_goals (try split_ifs) <;> first | rfl | contradiction | omega
  step4 := compatible_restrict _ _
  step5 := by
    rintro ⟨i,hi⟩ hM hC
    have hh := (middle_mem m ⟨i,hi⟩).mp hM
    change i=0 ∨ i=1 ∨ i=2*m at hh
    rcases hh with hh | hh | hh <;> subst i
    all_goals simp only [Flag.restrict, Data.firstCommonFlag, Data.secondCommonFlag,
      five, ofBounds, fiveNodes]
    all_goals (try split_ifs) <;> first | rfl | contradiction | omega
  step6 := by
    rintro ⟨i,hi⟩ hC hO
    have hh := (output_mem m ⟨i,hi⟩).mp hO
    change i=0 ∨ i=m ∨ i=m+1 at hh
    rcases hh with hh | hh | hh <;> subst i
    all_goals simp only [Data.secondCommonFlag, five, ofBounds, fiveNodes]
    all_goals (try split_ifs) <;> first | rfl | contradiction | omega

theorem Data.toSix_toData (d : Data hm source target) :
    (d.toSixGallery hm).toData hm = d := by
  apply Data.ext
  all_goals simp only [SixGallery.toData, Data.toSixGallery, Family.L, Family.I, Family.K, Family.H, atNode,
    Data.firstFlag, Data.firstCommonFlag, three, five, ofBounds, threeNodes, fiveNodes]
  all_goals (try split_ifs) <;> first | rfl | contradiction | omega

private theorem first_reconstruct (g : SixGallery source target) :
    (g.toData hm).firstFlag hm = g.first := by
  apply Flag.ext
  funext i
  obtain ⟨⟨i,hi⟩,hO⟩ := i
  have hh := (output_mem m ⟨i,hi⟩).mp hO
  change i=0 ∨ i=m ∨ i=m+1 at hh
  rcases hh with hh | hh | hh <;> subst i
  all_goals simp only [Data.firstFlag, three, ofBounds, threeNodes, SixGallery.toData,
    Family.I, Family.K, atNode]
  all_goals (try split_ifs) <;> first | rfl | exact g.step1 _ _ _ | contradiction | omega

private theorem firstCommon_reconstruct (g : SixGallery source target) :
    (g.toData hm).firstCommonFlag hm = g.firstCommon := by
  apply Flag.ext
  funext i
  obtain ⟨⟨i,hi⟩,hC⟩ := i
  have hh := (common_mem m ⟨i,hi⟩).mp hC
  change i=0 ∨ i=1 ∨ i=m ∨ i=m+1 ∨ i=2*m at hh
  rcases hh with hh | hh | hh | hh | hh <;> subst i
  all_goals simp only [Data.firstCommonFlag, five, ofBounds, fiveNodes, SixGallery.toData,
    Family.L, Family.I, Family.K, Family.H, atNode]
  all_goals (try split_ifs) <;> first | rfl | exact (common_zero hm g).symm |
    exact first_common hm g m (Or.inl rfl) |
    exact first_common hm g (m+1) (Or.inr rfl) | contradiction | omega

private theorem secondCommon_reconstruct (g : SixGallery source target) :
    (g.toData hm).secondCommonFlag hm = g.secondCommon := by
  apply Flag.ext
  funext i
  obtain ⟨⟨i,hi⟩,hC⟩ := i
  have hh := (common_mem m ⟨i,hi⟩).mp hC
  change i=0 ∨ i=1 ∨ i=m ∨ i=m+1 ∨ i=2*m at hh
  rcases hh with hh | hh | hh | hh | hh <;> subst i
  all_goals simp only [Data.secondCommonFlag, five, ofBounds, fiveNodes, SixGallery.toData,
    Family.L, Family.I, Family.K, Family.H, atNode]
  all_goals (try split_ifs) <;> first | rfl | exact (g.step6 _ _ _).symm |
    exact common_common hm g 1 (Or.inr (Or.inl rfl)) |
    exact common_common hm g (2*m) (Or.inr (Or.inr rfl)) | contradiction | omega

/-- The six partial flags contain exactly the four lattice choices in the
incidence description. This is the original mask reduction, proved here. -/
def sixDataEquiv : SixGallery source target ≃ Data hm source target where
  toFun := SixGallery.toData hm
  invFun := Data.toSixGallery hm
  right_inv := Data.toSix_toData hm
  left_inv g := by
    apply SixGallery.ext
    · exact first_reconstruct hm g
    · change ((g.toData hm).firstFlag hm).restrict J_sub_O = g.cyclic
      rw [first_reconstruct hm g]
      exact restrict_eq_of_compatible _ _ _ g.step2
    · exact firstCommon_reconstruct hm g
    · change ((g.toData hm).firstCommonFlag hm).restrict M_sub_C = g.middle
      rw [firstCommon_reconstruct hm g]
      exact restrict_eq_of_compatible _ _ _ g.step4
    · exact secondCommon_reconstruct hm g

end Guralnick.LatticeFlags.Family
