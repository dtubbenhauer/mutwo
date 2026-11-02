import Guralnick.CanonicalFlagAuxiliary
import Guralnick.LatticeRigidity

/-! # The retained-line gallery on actual lattices and its finite quotient -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Guralnick.CanonicalOneLineFlags
open LaurentLattice LatticeGallery LatticeFlags CanonicalChains CanonicalFlagAuxiliary

variable {k : Type} [Field k] {n : ℕ}

structure Data (A B F : Lattice k n) (j : ℕ) where
  L : Lattice k n
  U : Lattice k n
  target_le_line : B ≤ L
  line_le_F : L ≤ F
  line_le_U : L ≤ U
  source_le_U : A ≤ U
  U_le_source_period : U.space ≤ expand (shift k n) A.space
  U_le_target_period : U.space ≤ expand (shift k n) B.space
  degree_L : degree k n L = 1
  degree_U : degree k n U = j

@[ext] theorem Data.ext {A B F : Lattice k n} {j : ℕ} {x y : Data A B F j}
    (hL : x.L=y.L) (hU : x.U=y.U) : x=y := by
  cases x; cases y; cases hL; cases hU; rfl

def Data.spherical {A B F : Lattice k n} {j : Fin n} (d : Data A B F j.val) :
    SphericalData A B j :=
  ⟨d.U,d.source_le_U,d.target_le_line.trans d.line_le_U,
    d.U_le_source_period,d.U_le_target_period,d.degree_U⟩

def finiteF (B F : Lattice k n) (hBF : B≤F)
    (hFB : F.space≤expand (shift k n) B.space) : Submodule k (quotientSpace B) :=
  (quotientIso B).symm ⟨F.space,hBF,hFB⟩

def toFinite (T : Theory k n) {A B F : Lattice k n}
    (hB : degree k n B=0) (h : EndpointBounds A B)
    (hBF : B≤F) (hFB : F.space≤expand (shift k n) B.space) (j : Fin n)
    (d : Data A B F j.val) :
    GalleryCounting.OneLineGallery (finiteLower A B h) (finiteUpper A B h)
      (finiteF B F hBF hFB) j.val := by
  let U := sphericalToFinite T hB h j d.spherical
  let LX : Set.Icc B.space (expand (shift k n) B.space) :=
    ⟨d.L.space,d.target_le_line,
      (show d.L.space≤d.U.space from d.line_le_U).trans d.U_le_target_period⟩
  refine ⟨(quotientIso B).symm LX, U.val, ?_, U.property.2.2, ?_, ?_, U.property.1,
    U.property.2.1⟩
  · have hd := quotient_dimension T B d.L d.target_le_line LX.property.2
    rw [hB, sub_zero, d.degree_L] at hd
    exact_mod_cast hd
  · exact (quotientIso B).symm.monotone (show LX ≤ ⟨F.space,hBF,hFB⟩ from d.line_le_F)
  · exact (quotientIso B).symm.monotone
      (show LX ≤ ⟨d.U.space,d.spherical.target_le,d.U_le_target_period⟩ from d.line_le_U)

def fromFinite (T : Theory k n) {A B F : Lattice k n}
    (hB : degree k n B=0) (h : EndpointBounds A B)
    (hBF : B≤F) (hFB : F.space≤expand (shift k n) B.space) (j : Fin n)
    (d : GalleryCounting.OneLineGallery (finiteLower A B h) (finiteUpper A B h)
      (finiteF B F hBF hFB) j.val) : Data A B F j.val := by
  let U := sphericalFromFinite T hB h j ⟨d.U,d.I₀_le_U,d.U_le_K₀,d.U_dim⟩
  let LX := quotientIso B d.L
  let L := lift T B LX
  have hL : L.space=LX.val := lift_space T B LX
  have hU : U.U.space=(quotientIso B d.U).val := lift_space T B _
  have hBL : B≤L := by change B.space≤L.space; rw [hL]; exact LX.property.1
  have hLB : L.space≤expand (shift k n) B.space := by rw [hL]; exact LX.property.2
  refine ⟨L,U.U,hBL,?_,?_,U.source_le,U.le_source_period,U.le_target_period,?_,U.degree_U⟩
  · change L.space≤F.space
    rw [hL]
    have hd := (quotientIso B).monotone d.line_le_F
    simpa only [finiteF, OrderIso.apply_symm_apply] using hd
  · change L.space≤U.U.space
    rw [hL,hU]
    exact (quotientIso B).monotone d.line_le_U
  · have hd := quotient_dimension T B L hBL hLB
    rw [hB, sub_zero] at hd
    have hX : (⟨L.space,hBL,hLB⟩ : Set.Icc B.space (expand (shift k n) B.space)) = LX :=
      Subtype.ext hL
    rw [hX] at hd
    dsimp only [LX] at hd
    rw [OrderIso.symm_apply_apply,d.line_dim] at hd
    exact hd.symm

private theorem finite_ext {V : Type*} [AddCommGroup V] [Module k V]
    {I K F : Submodule k V} {j : ℕ} {x y : GalleryCounting.OneLineGallery I K F j}
    (hL : x.L=y.L) (hU : x.U=y.U) : x=y := by
  cases x; cases y; cases hL; cases hU; rfl

def finiteEquiv (T : Theory k n) {A B F : Lattice k n}
    (hB : degree k n B=0) (h : EndpointBounds A B)
    (hBF : B≤F) (hFB : F.space≤expand (shift k n) B.space) (j : Fin n) :
    Data A B F j.val ≃ GalleryCounting.OneLineGallery
      (finiteLower A B h) (finiteUpper A B h) (finiteF B F hBF hFB) j.val where
  toFun := toFinite T hB h hBF hFB j
  invFun := fromFinite T hB h hBF hFB j
  left_inv d := by
    apply Data.ext
    · apply Lattice.space_injective
      change (lift T B _).space=d.L.space
      rw [lift_space]
      simp only [toFinite, OrderIso.apply_symm_apply]
    · have he := (sphericalFiniteEquiv T hB h j).left_inv d.spherical
      exact congrArg SphericalData.U he
  right_inv d := by
    apply finite_ext
    · change (quotientIso B).symm _ = d.L
      apply (quotientIso B).injective
      rw [OrderIso.apply_symm_apply]
      apply Subtype.ext
      exact lift_space T B _
    · have he := (sphericalFiniteEquiv T hB h j).right_inv
        ⟨d.U,d.I₀_le_U,d.U_le_K₀,d.U_dim⟩
      exact congrArg Subtype.val he

/-- A three-position partial flag, allowing the final position to equal
one. In the coincident case the last lattice is recovered using degree
rigidity, not by silently deleting a distinct choice. -/
def threeFlag (hn : 1<n) (t : Fin n) (ht : 1≤t.val) (S : Finset (Fin n))
    (hS : ∀ b, b∈S ↔ b=(⟨0,Nat.zero_lt_of_lt hn⟩ : Fin n) ∨ b=⟨1,hn⟩ ∨ b=t)
    (A B C : Lattice k n) (hAB : A≤B) (hBC : B≤C)
    (hCA : C.space≤expand (shift k n) A.space)
    (hA : degree k n A=0) (hB : degree k n B=1) (hC : degree k n C=t.val) :
    Flag k n S := by
  let nodes : {b // b∈S} → Lattice k n :=
    fun b => if b.val.val=0 then A else if b.val.val=1 then B else C
  refine ofBounds nodes A C hCA ?_ ?_ ?_ ?_
  · intro b
    dsimp [nodes]
    split_ifs <;> first | exact le_rfl | exact hAB | exact hAB.trans hBC
  · intro b
    dsimp [nodes]
    split_ifs <;> first | exact le_rfl | exact hBC | exact hAB.trans hBC
  · intro a b hab
    change a.val.val≤b.val.val at hab
    rcases (hS a.val).mp a.property with ha | ha | ha
    all_goals rcases (hS b.val).mp b.property with hb | hb | hb
    all_goals simp only [nodes,ha,hb,Fin.val_mk] at *
    all_goals split_ifs <;> first | contradiction | exact le_rfl | exact hAB | exact hBC | exact hAB.trans hBC | omega
  · intro b
    rcases (hS b.val).mp b.property with hb | hb | hb
    all_goals simp only [nodes,hb]
    all_goals split_ifs <;> simp_all

theorem threeFlag_zero (hn) (t : Fin n) (ht S hS) (A B C : Lattice k n)
    (hAB hBC hCA hA hB hC) (hi : (⟨0,Nat.zero_lt_of_lt hn⟩ : Fin n)∈S) :
    (threeFlag hn t ht S hS A B C hAB hBC hCA hA hB hC).node ⟨⟨0,Nat.zero_lt_of_lt hn⟩,hi⟩=A := by
  simp [threeFlag,ofBounds]

theorem threeFlag_one (hn) (t : Fin n) (ht S hS) (A B C : Lattice k n)
    (hAB hBC hCA hA hB hC) (hi : (⟨1,hn⟩ : Fin n)∈S) :
    (threeFlag hn t ht S hS A B C hAB hBC hCA hA hB hC).node ⟨⟨1,hn⟩,hi⟩=B := by
  simp [threeFlag,ofBounds]

theorem threeFlag_last (T : Theory k n) (hn) (t : Fin n) (ht S hS)
    (A B C : Lattice k n) (hAB hBC hCA hA hB hC) (hi : t∈S) :
    (threeFlag hn t ht S hS A B C hAB hBC hCA hA hB hC).node ⟨t,hi⟩=C := by
  by_cases ht1 : t.val=1
  · have hBCeq : B=C := T.eq_of_le_of_degree_eq hBC (by rw [hB,hC,ht1]; norm_num)
    simp [threeFlag,ofBounds,ht1,hBCeq]
  · simp [threeFlag,ofBounds,show t.val≠0 by omega,ht1]

variable (hn : 1<n) (j f : Fin n) (hj : 1≤j.val) (hf : 1≤f.val)

abbrev src (hn : 1<n) := CanonicalChains.source (Nat.zero_lt_of_lt hn)
abbrev cyc (j : Fin n) := omitNode j
abbrev mid (hn : 1<n) := retainedLine (Nat.zero_lt_of_lt hn)
abbrev out (hn : 1<n) (f : Fin n) := twoRow (Nat.zero_lt_of_lt hn) f

theorem mid_mask (b : Fin n) :
    b∈retained (mid hn) ↔ b=(⟨0,Nat.zero_lt_of_lt hn⟩ : Fin n) ∨ b=⟨1,hn⟩ := by
  simp [mid,retained,retainedLine,CanonicalChains.source,omitNode,Fin.ext_iff]
  tauto

theorem out_mask (b : Fin n) :
    b∈retained (out hn f) ↔ b=(⟨0,Nat.zero_lt_of_lt hn⟩ : Fin n) ∨ b=f := by
  change b∈retained (meet (CanonicalChains.source (Nat.zero_lt_of_lt hn)) (omitNode f)) ↔ _
  rw [retained_meet]
  exact or_congr (retained_omit _ _) (retained_omit _ _)

theorem first_mask (b : Fin n) :
    b∈retained (meet (src hn) (cyc j)) ↔ b=(⟨0,Nat.zero_lt_of_lt hn⟩ : Fin n) ∨ b=j := by
  rw [retained_meet]
  exact or_congr (retained_omit _ _) (retained_omit _ _)

theorem common_mask (b : Fin n) :
    b∈retained (meet (cyc j) (mid hn)) ↔
      b=(⟨0,Nat.zero_lt_of_lt hn⟩ : Fin n) ∨ b=⟨1,hn⟩ ∨ b=j := by
  rw [retained_meet,retained_omit,mid_mask]
  tauto

theorem last_mask (b : Fin n) :
    b∈retained (meet (mid hn) (out hn f)) ↔
      b=(⟨0,Nat.zero_lt_of_lt hn⟩ : Fin n) ∨ b=⟨1,hn⟩ ∨ b=f := by
  rw [retained_meet,mid_mask,out_mask]
  tauto

variable (source : Flag k n (retained (src hn))) (target : Flag k n (retained (out hn f)))

def targetBase : Lattice k n :=
  target.node ⟨⟨0,Nat.zero_lt_of_lt hn⟩,(out_mask hn f _).mpr (Or.inl rfl)⟩

def targetF : Lattice k n := target.node ⟨f,(out_mask hn f _).mpr (Or.inr rfl)⟩

def Expanded : Type :=
  (middle : Flag k n (retained (mid hn))) ×
    ((cyclic : Flag k n (retained (cyc j))) ×
      ((srcFlag : Flag k n (retained (src hn))) × PLift (source=srcFlag) ×
        {first : Flag k n (retained (meet (src hn) (cyc j))) //
          Compatible srcFlag first ∧ Compatible first cyclic}) ×
      {common : Flag k n (retained (meet (cyc j) (mid hn))) //
        Compatible cyclic common ∧ Compatible common middle}) ×
    {last : Flag k n (retained (meet (mid hn) (out hn f))) //
      Compatible middle last ∧ Compatible last target}

/-- The six-map retained-line word determines the intermediate j-lattice
and the retained line-lattice, with every containment extracted from masks. -/
def toData (g : Expanded hn j f source target) :
    Data (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target) (targetF hn f target) j.val := by
  rcases g with ⟨middle,⟨cyclic,⟨srcFlag,heq,first⟩,common⟩,last⟩
  obtain ⟨rfl⟩ := heq
  let zero : Fin n := ⟨0,Nat.zero_lt_of_lt hn⟩
  let one : Fin n := ⟨1,hn⟩
  let LL := middle.node ⟨one,(mid_mask hn one).mpr (Or.inr rfl)⟩
  let UU := singleNode j cyclic
  have hc0 : common.val.node ⟨zero,(common_mask hn j zero).mpr (Or.inl rfl)⟩ =
      targetBase hn f target :=
    (common.property.2 zero _ ((mid_mask hn zero).mpr (Or.inl rfl))).trans
      ((last.property.1 zero ((mid_mask hn zero).mpr (Or.inl rfl))
          ((last_mask hn f zero).mpr (Or.inl rfl))).trans
        (last.property.2 zero ((last_mask hn f zero).mpr (Or.inl rfl)) _))
  have hc1 : common.val.node ⟨one,(common_mask hn j one).mpr (Or.inr (Or.inl rfl))⟩ = LL :=
    common.property.2 one _ _
  have hcj : common.val.node ⟨j,(common_mask hn j j).mpr (Or.inr (Or.inr rfl))⟩ = UU :=
    (common.property.1 j _ _).symm
  have hf0 : first.val.node ⟨zero,(first_mask hn j zero).mpr (Or.inl rfl)⟩ =
      singleNode zero source := (first.property.1 zero _ _).symm
  have hfj : first.val.node ⟨j,(first_mask hn j j).mpr (Or.inr rfl)⟩=UU :=
    first.property.2 j _ _
  have hl1 : last.val.node ⟨one,(last_mask hn f one).mpr (Or.inr (Or.inl rfl))⟩=LL :=
    (last.property.1 one _ _).symm
  have hlf : last.val.node ⟨f,(last_mask hn f f).mpr (Or.inr (Or.inr rfl))⟩ =
      targetF hn f target := last.property.2 f _ _
  refine ⟨LL,UU,?_,?_,?_,?_,?_,?_,middle.degree_eq _,singleNode_degree j cyclic⟩
  · rw [← hc0,← hc1]
    exact common.val.ordered _ _ (by change 0≤1; omega)
  · rw [← hl1,← hlf]
    exact last.val.ordered _ _ (by change 1≤f.val; exact hf)
  · rw [← hc1,← hcj]
    exact common.val.ordered _ _ (by change 1≤j.val; exact hj)
  · rw [← hf0,← hfj]
    exact first.val.ordered _ _ (by change 0≤j.val; omega)
  · rw [← hf0,← hfj]
    exact first.val.cyclic _ _
  · rw [← hc0,← hcj]
    exact common.val.cyclic _ _

def fromData (T : Theory k n)
    (d : Data (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target) (targetF hn f target) j.val) :
    Expanded hn j f source target := by
  let zero : Fin n := ⟨0,Nat.zero_lt_of_lt hn⟩
  let one : Fin n := ⟨1,hn⟩
  let A := singleNode zero source
  let B := targetBase hn f target
  let F := targetF hn f target
  have hA : degree k n A=0 := singleNode_degree zero source
  have hB : degree k n B=0 := target.degree_eq _
  have hF : degree k n F=f.val := target.degree_eq _
  have hBF : B≤F := target.ordered _ _ (by change 0≤f.val; omega)
  have hFB : F.space≤expand (shift k n) B.space := target.cyclic _ _
  have hLB : d.L.space≤expand (shift k n) B.space :=
    (show d.L.space≤d.U.space from d.line_le_U).trans d.U_le_target_period
  let middle := pairFlag zero one (by change 0<1; omega) (retained (mid hn))
    (mid_mask hn) B d.L d.target_le_line hLB hB d.degree_L
  let cyclic := singleFlag j d.U d.degree_U
  let first := pairFlag zero j (by change 0<j.val; omega) (retained (meet (src hn) (cyc j)))
    (first_mask hn j) A d.U d.source_le_U d.U_le_source_period hA d.degree_U
  let common := threeFlag hn j hj (retained (meet (cyc j) (mid hn))) (common_mask hn j)
    B d.L d.U d.target_le_line d.line_le_U d.U_le_target_period hB d.degree_L d.degree_U
  let last := threeFlag hn f hf (retained (meet (mid hn) (out hn f))) (last_mask hn f)
    B d.L F d.target_le_line d.line_le_F hFB hB d.degree_L hF
  refine ⟨middle,⟨cyclic,⟨source,⟨rfl⟩,⟨first,?_,?_⟩⟩,⟨common,?_,?_⟩⟩,⟨last,?_,?_⟩⟩
  · intro b hb hc
    have hb0 := (retained_omit zero b).mp hb
    subst b
    exact (pairFlag_node_left _ _ _ _ _ _ _ _ _ _ _ hc).symm
  · intro b hb hc
    have hbj := (retained_omit j b).mp hc
    subst b
    exact pairFlag_node_right _ _ _ _ _ _ _ _ _ _ _ hb
  · intro b hb hc
    have hbj := (retained_omit j b).mp hb
    subst b
    exact (threeFlag_last T _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc).symm
  · intro b hb hc
    rcases (mid_mask hn b).mp hc with hb0 | hb1
    · subst b
      exact (threeFlag_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb).trans
        (pairFlag_node_left _ _ _ _ _ _ _ _ _ _ _ hc).symm
    · subst b
      exact (threeFlag_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb).trans
        (pairFlag_node_right _ _ _ _ _ _ _ _ _ _ _ hc).symm
  · intro b hb hc
    rcases (mid_mask hn b).mp hb with hb0 | hb1
    · subst b
      exact (pairFlag_node_left _ _ _ _ _ _ _ _ _ _ _ hb).trans
        (threeFlag_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc).symm
    · subst b
      exact (pairFlag_node_right _ _ _ _ _ _ _ _ _ _ _ hb).trans
        (threeFlag_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc).symm
  · intro b hb hc
    rcases (out_mask hn f b).mp hc with hb0 | hbf
    · subst b
      exact threeFlag_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb
    · subst b
      exact threeFlag_last T _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb

theorem toData_fromData (T : Theory k n)
    (d : Data (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target) (targetF hn f target) j.val) :
    toData hn j f hj hf source target (fromData hn j f hj hf source target T d)=d := by
  apply Data.ext
  · rfl
  · rfl

/-- Two flags on the union mask coincide once their two restrictions coincide. -/
theorem compatible_unique {I J : ParabolicWeb.Index n}
    {A : Flag k n (retained I)} {B : Flag k n (retained J)}
    {F G : Flag k n (retained (meet I J))}
    (hAF : Compatible A F) (hFB : Compatible F B)
    (hAG : Compatible A G) (hGB : Compatible G B) : F=G := by
  apply LatticeFlags.Flag.ext
  funext b
  rcases (retained_meet I J b.val).mp b.property with hI | hJ
  · exact (hAF b.val hI b.property).symm.trans (hAG b.val hI b.property)
  · exact (hFB b.val b.property hJ).trans (hGB b.val b.property hJ).symm

theorem toData_injective : Function.Injective (toData hn j f hj hf source target) := by
  intro x y heq
  rcases x with ⟨mx,⟨cx,⟨sx,hex,fx⟩,qx⟩,lx⟩
  rcases y with ⟨my,⟨cy,⟨sy,hey,fy⟩,qy⟩,ly⟩
  obtain ⟨rfl⟩ := hex
  obtain ⟨rfl⟩ := hey
  have hU := congrArg Data.U heq
  change singleNode j cx = singleNode j cy at hU
  have hcyclic : cx=cy := by
    rw [← singleFlag_singleNode j cx,← singleFlag_singleNode j cy]
    congr 1
  subst cy
  have hL := congrArg Data.L heq
  have hmiddle : mx=my := by
    apply LatticeFlags.Flag.ext
    funext b
    rcases (mid_mask hn b.val).mp b.property with hb | hb
    · rcases b with ⟨b,hbmem⟩
      dsimp only at hb
      subst b
      let zero : Fin n := ⟨0,Nat.zero_lt_of_lt hn⟩
      have hlast : zero∈retained (meet (mid hn) (out hn f)) :=
        (last_mask hn f zero).mpr (Or.inl rfl)
      have hout : zero∈retained (out hn f) := (out_mask hn f zero).mpr (Or.inl rfl)
      exact ((lx.property.1 zero hbmem hlast).trans (lx.property.2 zero hlast hout)).trans
        ((ly.property.1 zero hbmem hlast).trans (ly.property.2 zero hlast hout)).symm
    · rcases b with ⟨b,hbmem⟩
      dsimp only at hb
      subst b
      exact hL
  subst my
  have hfirst : fx=fy := Subtype.ext (compatible_unique fx.property.1 fx.property.2
    fy.property.1 fy.property.2)
  have hcommon : qx=qy := Subtype.ext (compatible_unique qx.property.1 qx.property.2
    qy.property.1 qy.property.2)
  have hlast : lx=ly := Subtype.ext (compatible_unique lx.property.1 lx.property.2
    ly.property.1 ly.property.2)
  subst fy
  subst qy
  subst ly
  rfl

def expandedEquiv (T : Theory k n) :
    Expanded hn j f source target ≃
      Data (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source)
        (targetBase hn f target) (targetF hn f target) j.val :=
  Equiv.ofBijective (toData hn j f hj hf source target)
    ⟨toData_injective hn j f hj hf source target,
      fun d => ⟨fromData hn j f hj hf source target T d,
        toData_fromData hn j f hj hf source target T d⟩⟩

/-- The actual recursive parabolic flag gallery is precisely the pair of
lattices retained by the one-line web. -/
def oneLineGalleryEquiv (T : Theory k n) :
    FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target ≃
      Data (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source)
        (targetBase hn f target) (targetF hn f target) j.val :=
  (Equiv.cast (by simp only [oneLineChain,FlagConvolution.Gallery,Expanded])).trans
    (expandedEquiv hn j f hj hf source target T)

theorem targetBase_le_F : targetBase hn f target ≤ targetF hn f target :=
  target.ordered _ _ (by change 0≤f.val; omega)

theorem targetF_le_period : (targetF hn f target).space ≤
    expand (shift k n) (targetBase hn f target).space := target.cyclic _ _

def oneLineFiniteGalleryEquiv (T : Theory k n)
    (h : EndpointBounds (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target)) :
    FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target ≃
      GalleryCounting.OneLineGallery
        (finiteLower (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target) h)
        (finiteUpper (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target) h)
        (finiteF (targetBase hn f target) (targetF hn f target)
          (targetBase_le_F hn f target) (targetF_le_period hn f target)) j.val :=
  (oneLineGalleryEquiv hn j f hj hf source target T).trans
    (finiteEquiv T (target.degree_eq _) h (targetBase_le_F hn f target)
      (targetF_le_period hn f target) j)

include hj hf in
/-- The actual one-line flag word has the two-case Gaussian count. Only
intersection dimensions of its endpoints remain to be evaluated. -/
theorem one_line_gallery_count [Finite k] (T : Theory k n)
    [FiniteDimensional k (quotientSpace (targetBase hn f target))]
    [Finite (quotientSpace (targetBase hn f target))]
    (h : EndpointBounds (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target))
    (hcount : GalleryCounting.FiniteFlagCounts k (quotientSpace (targetBase hn f target)))
    (nn s d a b : ℤ)
    (hN : (Module.finrank k (finiteUpper (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source)
      (targetBase hn f target) h) : ℤ) -
      Module.finrank k (finiteLower (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source)
        (targetBase hn f target) h) = nn)
    (hs : (j.val : ℤ) - Module.finrank k (finiteLower
      (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source) (targetBase hn f target) h) = s)
    (ha : (Module.finrank k ((finiteLower (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source)
      (targetBase hn f target) h) ⊓ (finiteF (targetBase hn f target) (targetF hn f target)
        (targetBase_le_F hn f target) (targetF_le_period hn f target)) :
          Submodule k (quotientSpace (targetBase hn f target))) : ℤ) = a)
    (hc : (Module.finrank k ((finiteUpper (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source)
      (targetBase hn f target) h) ⊓ (finiteF (targetBase hn f target) (targetF hn f target)
        (targetBase_le_F hn f target) (targetF_le_period hn f target)) :
          Submodule k (quotientSpace (targetBase hn f target))) : ℤ) = d+b) :
    (Nat.card (FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f)
      source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ) (CanonicalAuxiliary.oneLineCount nn s d a b) := by
  rw [Nat.card_congr (oneLineFiniteGalleryEquiv hn j f hj hf source target T h)]
  exact GalleryCounting.one_line_count hcount (finiteLower_le_upper _ _ h) hN hs ha hc

end Guralnick.CanonicalOneLineFlags
