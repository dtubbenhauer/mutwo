import Guralnick.FlagConvolution
import Guralnick.FlagConstructors
import Guralnick.LatticeTheory
import Guralnick.RelativeDimensions
import Guralnick.GalleryCounting

/-!
# Auxiliary flag galleries as actual lattice configurations

These equivalences unpack the general convolution gallery for the auxiliary
chains. The intermediate choices are genuine Laurent-series lattices; their
finite quotient interpretation uses only the general interval-lifting theorem.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace Guralnick.CanonicalFlagAuxiliary

open LaurentLattice LatticeFlags CanonicalChains ParabolicWeb LatticeGallery

variable {k : Type} [Field k] {n : ℕ}

theorem retained_omit (i b : Fin n) : b ∈ retained (omitNode i) ↔ b=i := by
  simp [retained, omitNode]

theorem retained_meet (I J : Index n) (b : Fin n) :
    b ∈ retained (meet I J) ↔ b ∈ retained I ∨ b ∈ retained J := by
  simp [retained, meet]

def singleNode (i : Fin n) (F : Flag k n (retained (omitNode i))) : Lattice k n :=
  F.node ⟨i, (retained_omit i i).mpr rfl⟩

theorem singleNode_degree (i : Fin n) (F : Flag k n (retained (omitNode i))) :
    degree k n (singleNode i F) = i.val := F.degree_eq _

def singleFlag (i : Fin n) (A : Lattice k n) (hA : degree k n A = i.val) :
    Flag k n (retained (omitNode i)) where
  node _ := A
  ordered _ _ _ := le_rfl
  cyclic _ _ := stable k n A
  degree_eq b := by
    have hb := (retained_omit i b.val).mp b.property
    simpa only [hb] using hA

theorem singleNode_singleFlag (i : Fin n) (A : Lattice k n) (hA) :
    singleNode i (singleFlag i A hA) = A := rfl

theorem singleFlag_singleNode (i : Fin n) (F : Flag k n (retained (omitNode i))) :
    singleFlag i (singleNode i F) (singleNode_degree i F) = F := by
  apply LatticeFlags.Flag.ext
  funext b
  have hb := (retained_omit i b.val).mp b.property
  cases b
  dsimp only at hb
  subst hb
  rfl

/-- A two-node chain on any mask with the stated pair of types. -/
def pairFlag (i j : Fin n) (hij : i < j) (S : Finset (Fin n))
    (hS : ∀ b, b ∈ S ↔ b=i ∨ b=j) (A B : Lattice k n)
    (hAB : A ≤ B) (hBA : B.space ≤ expand (shift k n) A.space)
    (hA : degree k n A=i.val) (hB : degree k n B=j.val) : Flag k n S := by
  let nodes : {b // b∈S} → Lattice k n := fun b => if b.val=i then A else B
  refine ofBounds nodes A B hBA ?_ ?_ ?_ ?_
  · intro b
    dsimp [nodes]
    split_ifs <;> first | exact le_rfl | exact hAB
  · intro b
    dsimp [nodes]
    split_ifs <;> first | exact le_rfl | exact hAB
  · intro a b hab
    rcases (hS a.val).mp a.property with ha | ha
    all_goals rcases (hS b.val).mp b.property with hb | hb
    all_goals simp only [nodes, ha, hb]
    all_goals split_ifs <;> first | exact le_rfl | exact hAB | omega
  · intro b
    rcases (hS b.val).mp b.property with hb | hb
    · simp [nodes, hb, hA]
    · simp [nodes, hb, ne_of_gt hij, hB]

theorem pairFlag_node_left (i j : Fin n) (hij) (S) (hS) (A B : Lattice k n)
    (hAB hBA hA hB) (hi : i∈S) :
    (pairFlag i j hij S hS A B hAB hBA hA hB).node ⟨i,hi⟩ = A := by
  simp [pairFlag, ofBounds]

theorem pairFlag_node_right (i j : Fin n) (hij) (S) (hS) (A B : Lattice k n)
    (hAB hBA hA hB) (hj : j∈S) :
    (pairFlag i j hij S hS A B hAB hBA hA hB).node ⟨j,hj⟩ = B := by
  simp [pairFlag, ofBounds, ne_of_gt hij]

/-- An intermediate type-s lattice lying in both one-period intervals. -/
structure SphericalData (A B : Lattice k n) (s : Fin n) where
  U : Lattice k n
  source_le : A ≤ U
  target_le : B ≤ U
  le_source_period : U.space ≤ expand (shift k n) A.space
  le_target_period : U.space ≤ expand (shift k n) B.space
  degree_U : degree k n U = s.val

@[ext] theorem SphericalData.ext {A B : Lattice k n} {s : Fin n}
    {x y : SphericalData A B s} (h : x.U=y.U) : x=y := by
  cases x; cases y; cases h; rfl

variable (hn : 0<n) (s : Fin n) (hs : 0<s.val)
variable (source target : Flag k n (retained (CanonicalChains.source hn)))

abbrev sourceLattice : Lattice k n := singleNode ⟨0,hn⟩ source
abbrev targetLattice : Lattice k n := singleNode ⟨0,hn⟩ target

private theorem pair_source_mask (b : Fin n) :
    b ∈ retained (meet (CanonicalChains.source hn) (omitNode s)) ↔
      b=(⟨0,hn⟩ : Fin n) ∨ b=s := by
  rw [retained_meet]
  exact or_congr (retained_omit _ _) (retained_omit _ _)

private theorem pair_target_mask (b : Fin n) :
    b ∈ retained (meet (omitNode s) (CanonicalChains.source hn)) ↔
      b=(⟨0,hn⟩ : Fin n) ∨ b=s := by
  rw [retained_meet]
  simpa only [or_comm] using or_congr (retained_omit s b) (retained_omit ⟨0,hn⟩ b)

/-- The recursively defined gallery with its two steps expanded. -/
def SphericalExpanded : Type :=
  (middle : Flag k n (retained (omitNode s))) ×
    ((src : Flag k n (retained (CanonicalChains.source hn))) ×
      PLift (source=src) ×
      {first : Flag k n (retained (meet (CanonicalChains.source hn) (omitNode s))) //
        Compatible src first ∧ Compatible first middle}) ×
    {last : Flag k n (retained (meet (omitNode s) (CanonicalChains.source hn))) //
      Compatible middle last ∧ Compatible last target}

/-- Reading the intermediate lattice from the recursive convolution gallery. -/
def sphericalToData (g : SphericalExpanded hn s source target) :
    SphericalData (sourceLattice hn source) (targetLattice hn target) s := by
  rcases g with ⟨middle, ⟨src, heq, first⟩, last⟩
  obtain ⟨rfl⟩ := heq
  let iz : Fin n := ⟨0,hn⟩
  have hfirst0 : (first.val.node ⟨iz, (pair_source_mask hn s iz).mpr (Or.inl rfl)⟩) =
      sourceLattice hn source := (first.property.1 iz _ _).symm
  have hfirsts : first.val.node ⟨s, (pair_source_mask hn s s).mpr (Or.inr rfl)⟩ =
      singleNode s middle := first.property.2 s _ _
  have hlast0 : last.val.node ⟨iz, (pair_target_mask hn s iz).mpr (Or.inl rfl)⟩ =
      targetLattice hn target := last.property.2 iz _ _
  have hlasts : last.val.node ⟨s, (pair_target_mask hn s s).mpr (Or.inr rfl)⟩ =
      singleNode s middle := (last.property.1 s _ _).symm
  refine ⟨singleNode s middle, ?_, ?_, ?_, ?_, singleNode_degree s middle⟩
  · rw [← hfirst0, ← hfirsts]
    exact first.val.ordered _ _ (by change 0≤s.val; omega)
  · rw [← hlast0, ← hlasts]
    exact last.val.ordered _ _ (by change 0≤s.val; omega)
  · rw [← hfirst0, ← hfirsts]
    exact first.val.cyclic _ _
  · rw [← hlast0, ← hlasts]
    exact last.val.cyclic _ _

def sphericalFromData
    (d : SphericalData (sourceLattice hn source) (targetLattice hn target) s) :
    SphericalExpanded hn s source target := by
  let mid := singleFlag s d.U d.degree_U
  let first := pairFlag ⟨0,hn⟩ s (show (⟨0,hn⟩ : Fin n)<s from hs)
    (retained (meet (CanonicalChains.source hn) (omitNode s))) (pair_source_mask hn s)
    (sourceLattice hn source) d.U d.source_le d.le_source_period
    (singleNode_degree ⟨0,hn⟩ source) d.degree_U
  let last := pairFlag ⟨0,hn⟩ s (show (⟨0,hn⟩ : Fin n)<s from hs)
    (retained (meet (omitNode s) (CanonicalChains.source hn))) (pair_target_mask hn s)
    (targetLattice hn target) d.U d.target_le d.le_target_period
    (singleNode_degree ⟨0,hn⟩ target) d.degree_U
  refine ⟨mid, ⟨source, ⟨rfl⟩, ⟨first, ?_, ?_⟩⟩, ⟨last, ?_, ?_⟩⟩
  · intro b hb hc
    have hb0 := (retained_omit ⟨0,hn⟩ b).mp hb
    subst b
    exact (pairFlag_node_left _ _ _ _ _ _ _ _ _ _ _ hc).symm
  · intro b hb hc
    have hbs := (retained_omit s b).mp hc
    subst b
    exact pairFlag_node_right _ _ _ _ _ _ _ _ _ _ _ hb
  · intro b hb hc
    have hbs := (retained_omit s b).mp hb
    subst b
    exact (pairFlag_node_right _ _ _ _ _ _ _ _ _ _ _ hc).symm
  · intro b hb hc
    have hb0 := (retained_omit ⟨0,hn⟩ b).mp hc
    subst b
    exact pairFlag_node_left _ _ _ _ _ _ _ _ _ _ _ hb

theorem sphericalToFrom
    (d : SphericalData (sourceLattice hn source) (targetLattice hn target) s) :
    sphericalToData hn s hs source target (sphericalFromData hn s hs source target d) = d := by
  apply SphericalData.ext
  rfl

private theorem pairFlag_eq_from_compatibility
    (i j : Fin n) (hij : i<j) (S : Finset (Fin n))
    (hS : ∀ b, b∈S ↔ b=i ∨ b=j)
    (A B : Lattice k n) (hAB hBA hA hB)
    (F : Flag k n S)
    (hleft : ∀ hi : i∈S, F.node ⟨i,hi⟩ = A)
    (hright : ∀ hj : j∈S, F.node ⟨j,hj⟩ = B) :
    pairFlag i j hij S hS A B hAB hBA hA hB = F := by
  apply LatticeFlags.Flag.ext
  funext b
  rcases (hS b.val).mp b.property with hi | hj
  · rcases b with ⟨b,hb⟩
    dsimp only at hi
    subst b
    exact (pairFlag_node_left _ _ _ _ _ _ _ _ _ _ _ hb).trans (hleft hb).symm
  · rcases b with ⟨b,hb⟩
    dsimp only at hj
    subst b
    exact (pairFlag_node_right _ _ _ _ _ _ _ _ _ _ _ hb).trans (hright hb).symm

theorem sphericalToData_injective :
    Function.Injective (sphericalToData hn s hs source target) := by
  intro x y heq
  rcases x with ⟨mx, ⟨sx, hex, fx⟩, lx⟩
  rcases y with ⟨my, ⟨sy, hey, fy⟩, ly⟩
  obtain ⟨rfl⟩ := hex
  obtain ⟨rfl⟩ := hey
  have hU := congrArg SphericalData.U heq
  change singleNode s mx = singleNode s my at hU
  have hmid : mx=my := by
    rw [← singleFlag_singleNode s mx, ← singleFlag_singleNode s my]
    congr 1
  subst my
  have hfirst : fx.val=fy.val := by
    apply LatticeFlags.Flag.ext
    funext b
    rcases (pair_source_mask hn s b.val).mp b.property with hb | hb
    · rcases b with ⟨b,hbmem⟩
      dsimp only at hb
      subst b
      exact (fx.property.1 ⟨0,hn⟩ ((retained_omit _ _).mpr rfl) hbmem).symm.trans (fy.property.1 ⟨0,hn⟩ ((retained_omit _ _).mpr rfl) hbmem)
    · rcases b with ⟨b,hbmem⟩
      dsimp only at hb
      subst b
      exact (fx.property.2 s hbmem ((retained_omit s s).mpr rfl)).trans (fy.property.2 s hbmem ((retained_omit s s).mpr rfl)).symm
  have hlast : lx.val=ly.val := by
    apply LatticeFlags.Flag.ext
    funext b
    rcases (pair_target_mask hn s b.val).mp b.property with hb | hb
    · rcases b with ⟨b,hbmem⟩
      dsimp only at hb
      subst b
      exact (lx.property.2 ⟨0,hn⟩ hbmem ((retained_omit _ _).mpr rfl)).trans (ly.property.2 ⟨0,hn⟩ hbmem ((retained_omit _ _).mpr rfl)).symm
    · rcases b with ⟨b,hbmem⟩
      dsimp only at hb
      subst b
      exact (lx.property.1 s ((retained_omit s s).mpr rfl) hbmem).symm.trans (ly.property.1 s ((retained_omit s s).mpr rfl) hbmem)
  have hf : fx=fy := Subtype.ext hfirst
  have hl : lx=ly := Subtype.ext hlast
  subst fy
  subst ly
  rfl

def sphericalExpandedEquiv :
    SphericalExpanded hn s source target ≃
      SphericalData (sourceLattice hn source) (targetLattice hn target) s :=
  Equiv.ofBijective (sphericalToData hn s hs source target)
    ⟨sphericalToData_injective hn s hs source target,
      fun d => ⟨sphericalFromData hn s hs source target d,
        sphericalToFrom hn s hs source target d⟩⟩

def sphericalGalleryEquiv :
    FlagConvolution.Gallery k (sphericalChain hn s) source target ≃
      SphericalData (sourceLattice hn source) (targetLattice hn target) s :=
  (Equiv.cast (by simp only [sphericalChain, FlagConvolution.Gallery, SphericalExpanded])).trans
    (sphericalExpandedEquiv hn s hs source target)

/-- The common one-period envelope forced by a nonempty spherical gallery. -/
structure EndpointBounds (A B : Lattice k n) : Prop where
  source_le : A.space ≤ expand (shift k n) B.space
  target_le : B.space ≤ expand (shift k n) A.space

namespace SphericalData

def endpointBounds {A B : Lattice k n} {s : Fin n} (d : SphericalData A B s) :
    EndpointBounds A B :=
  ⟨(show A.space ≤ d.U.space from d.source_le).trans d.le_target_period,
    (show B.space ≤ d.U.space from d.target_le).trans d.le_source_period⟩

end SphericalData

variable {hn s hs source target}

abbrev quotientSpace (B : Lattice k n) := QuotientSpace B.space (expand (shift k n) B.space)

def quotientIso (B : Lattice k n) :
    Submodule k (quotientSpace B) ≃o Set.Icc B.space (expand (shift k n) B.space) :=
  quotientIntervalIso B.space (expand (shift k n) B.space) (stable k n B)

def lowerEndpoint (A B : Lattice k n) (h : EndpointBounds A B) :
    Set.Icc B.space (expand (shift k n) B.space) :=
  ⟨A.space ⊔ B.space, le_sup_right, sup_le h.source_le (stable k n B)⟩

def upperEndpoint (A B : Lattice k n) (h : EndpointBounds A B) :
    Set.Icc B.space (expand (shift k n) B.space) :=
  ⟨expand (shift k n) A.space ⊓ expand (shift k n) B.space,
    le_inf h.target_le (stable k n B), inf_le_right⟩

def finiteLower (A B : Lattice k n) (h : EndpointBounds A B) : Submodule k (quotientSpace B) :=
  (quotientIso B).symm (lowerEndpoint A B h)

def finiteUpper (A B : Lattice k n) (h : EndpointBounds A B) : Submodule k (quotientSpace B) :=
  (quotientIso B).symm (upperEndpoint A B h)

def lift (T : Theory k n) (B : Lattice k n)
    (X : Set.Icc B.space (expand (shift k n) B.space)) : Lattice k n :=
  ((T.intervalIso B).symm X).val

theorem lift_space (T : Theory k n) (B : Lattice k n)
    (X : Set.Icc B.space (expand (shift k n) B.space)) : (lift T B X).space = X.val :=
  congrArg Subtype.val ((T.intervalIso B).apply_symm_apply X)

theorem quotient_dimension (T : Theory k n) (B U : Lattice k n)
    (hBU : B≤U) (hUB : U.space≤expand (shift k n) B.space) :
    (Module.finrank k ((quotientIso B).symm ⟨U.space,hBU,hUB⟩) : ℤ) =
      degree k n U-degree k n B := by
  have hq := quotientImage_finrank B.space (expand (shift k n) B.space)
    (stable k n B) U.space hBU hUB
  change Module.finrank k ((quotientIso B).symm ⟨U.space,hBU,hUB⟩) = _ at hq
  rw [hq]
  exact T.dimension_degree B U hBU

def sphericalToFinite (T : Theory k n) {A B : Lattice k n}
    (hB : degree k n B=0) (h : EndpointBounds A B) (s : Fin n)
    (d : SphericalData A B s) :
    GalleryCounting.IntermediateSubspace (finiteLower A B h) (finiteUpper A B h) s.val := by
  let X : Set.Icc B.space (expand (shift k n) B.space) :=
    ⟨d.U.space,d.target_le,d.le_target_period⟩
  refine ⟨(quotientIso B).symm X, ?_, ?_, ?_⟩
  · have hh : lowerEndpoint A B h ≤ X := by
      change A.space ⊔ B.space ≤ d.U.space
      exact sup_le d.source_le d.target_le
    exact (quotientIso B).symm.monotone hh
  · have hh : X ≤ upperEndpoint A B h := le_inf d.le_source_period d.le_target_period
    exact (quotientIso B).symm.monotone hh
  · have hd := quotient_dimension T B d.U d.target_le d.le_target_period
    rw [hB, sub_zero, d.degree_U] at hd
    exact_mod_cast hd

def sphericalFromFinite (T : Theory k n) {A B : Lattice k n}
    (hB : degree k n B=0) (h : EndpointBounds A B) (s : Fin n)
    (d : GalleryCounting.IntermediateSubspace (finiteLower A B h) (finiteUpper A B h) s.val) :
    SphericalData A B s := by
  let X := quotientIso B d.val
  let U := lift T B X
  have hlow : (lowerEndpoint A B h).val ≤ X.val := by
    have ht := (quotientIso B).monotone d.property.1
    simpa only [finiteLower, OrderIso.apply_symm_apply] using ht
  have hupp : X.val ≤ (upperEndpoint A B h).val := by
    have ht := (quotientIso B).monotone d.property.2.1
    simpa only [finiteUpper, OrderIso.apply_symm_apply] using ht
  have hU : U.space=X.val := lift_space T B X
  have hBU : B≤U := by change B.space≤U.space; rw [hU]; exact X.property.1
  have hUB : U.space≤expand (shift k n) B.space := by rw [hU]; exact X.property.2
  refine ⟨U, ?_, hBU, ?_, hUB, ?_⟩
  · change A.space≤U.space
    rw [hU]
    exact le_sup_left.trans hlow
  · rw [hU]
    exact hupp.trans inf_le_left
  · have hd := quotient_dimension T B U hBU hUB
    rw [hB, sub_zero] at hd
    have hX : (⟨U.space,hBU,hUB⟩ : Set.Icc B.space (expand (shift k n) B.space)) = X :=
      Subtype.ext hU
    rw [hX] at hd
    dsimp only [X] at hd
    rw [OrderIso.symm_apply_apply, d.property.2.2] at hd
    exact hd.symm

def sphericalFiniteEquiv (T : Theory k n) {A B : Lattice k n}
    (hB : degree k n B=0) (h : EndpointBounds A B) (s : Fin n) :
    SphericalData A B s ≃
      GalleryCounting.IntermediateSubspace (finiteLower A B h) (finiteUpper A B h) s.val where
  toFun := sphericalToFinite T hB h s
  invFun := sphericalFromFinite T hB h s
  left_inv d := by
    apply SphericalData.ext
    apply Lattice.space_injective
    change (lift T B _).space = d.U.space
    rw [lift_space]
    simp only [sphericalToFinite, OrderIso.apply_symm_apply]
  right_inv d := by
    apply Subtype.ext
    change (quotientIso B).symm _ = d.val
    apply (quotientIso B).injective
    rw [OrderIso.apply_symm_apply]
    apply Subtype.ext
    exact lift_space T B _

theorem finiteLower_le_upper (A B : Lattice k n) (h : EndpointBounds A B) :
    finiteLower A B h ≤ finiteUpper A B h := by
  have hb : lowerEndpoint A B h ≤ upperEndpoint A B h := by
    change A.space ⊔ B.space ≤ expand (shift k n) A.space ⊓ expand (shift k n) B.space
    exact sup_le (le_inf (stable k n A) h.source_le)
      (le_inf h.target_le (stable k n B))
  change (quotientIso B).symm (lowerEndpoint A B h) ≤
    (quotientIso B).symm (upperEndpoint A B h)
  exact (quotientIso B).symm.monotone hb

/-- Every choice in the spherical convolution word is exactly one subspace
in the finite endpoint quotient, with the required dimension. -/
def sphericalFiniteGalleryEquiv (T : Theory k n) (hn : 0<n) (s : Fin n) (hs : 0<s.val)
    (source target : Flag k n (retained (CanonicalChains.source hn)))
    (h : EndpointBounds (sourceLattice hn source) (targetLattice hn target)) :
    FlagConvolution.Gallery k (sphericalChain hn s) source target ≃
      GalleryCounting.IntermediateSubspace
        (finiteLower (sourceLattice hn source) (targetLattice hn target) h)
        (finiteUpper (sourceLattice hn source) (targetLattice hn target) h) s.val :=
  (sphericalGalleryEquiv hn s hs source target).trans
    (sphericalFiniteEquiv T (singleNode_degree ⟨0,hn⟩ target) h s)

/-- The full-spherical count is a conclusion about the actual convolution
gallery. The remaining rank hypotheses are exactly endpoint intersection
ranks, to be supplied by the generic orbit/matrix dictionary. -/
theorem spherical_gallery_count [Finite k] (T : Theory k n)
    (hn : 0<n) (s : Fin n) (hs : 0<s.val)
    (source target : Flag k n (retained (CanonicalChains.source hn)))
    [FiniteDimensional k (quotientSpace (targetLattice hn target))]
    [Finite (quotientSpace (targetLattice hn target))]
    (h : EndpointBounds (sourceLattice hn source) (targetLattice hn target))
    (hcount : GalleryCounting.FiniteFlagCounts k (quotientSpace (targetLattice hn target)))
    (r : ℕ)
    (hI : Module.finrank k (finiteLower (sourceLattice hn source) (targetLattice hn target) h)=r)
    (hK : Module.finrank k (finiteUpper (sourceLattice hn source) (targetLattice hn target) h)=n-r) :
    (Nat.card (FlagConvolution.Gallery k (sphericalChain hn s) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ) (CanonicalGallery.qGauss ((n : ℤ)-2*r) ((s.val : ℤ)-r)) := by
  rw [Nat.card_congr (sphericalFiniteGalleryEquiv T hn s hs source target h)]
  exact GalleryCounting.spherical_count hcount (finiteLower_le_upper _ _ h) hI hK

end Guralnick.CanonicalFlagAuxiliary
