import Guralnick.SixFlagData

/-! # Passing the four genuine lattice choices to the finite quotient -/
noncomputable section
namespace Guralnick.LatticeFlags.Family
open LaurentLattice LatticeGallery
variable {k : Type*} [Field k] {m : ℕ} (hm : 2 ≤ m)
  (source : Flag k (2*m+1) (S m)) (target : Flag k (2*m+1) (O m))

/-- These bounds are forced by any six-map gallery. -/
structure Bounds : Prop where
  source_le : (sourceNode source).space ≤ expand (shift k (2*m+1)) (targetNode target).space
  target_le : (targetNode target).space ≤ expand (shift k (2*m+1)) (sourceNode source).space

variable {source target}

def SixGallery.bounds (g : SixGallery source target) : Bounds source target :=
  ⟨(endpoint_bounds hm g).1,(endpoint_bounds hm g).2⟩

abbrev base (target : Flag k (2*m+1) (O m)) := (targetNode target).space
abbrev upper (target : Flag k (2*m+1) (O m)) := expand (shift k (2*m+1)) (targetNode target).space

def I0 (h : Bounds source target) : Set.Icc (base target) (upper target) :=
  ⟨(sourceNode source).space ⊔ (targetNode target).space, le_sup_right,
    sup_le h.source_le (stable k _ _)⟩

def K0 (h : Bounds source target) : Set.Icc (base target) (upper target) :=
  ⟨expand (shift k (2*m+1)) (sourceNode source).space ⊓ upper target,
    le_inf h.target_le (stable k _ _), inf_le_right⟩

def endpointF : Set.Icc (base target) (upper target) :=
  ⟨(targetF target).space, target.ordered _ _ (by simp only [Fin.le_def]; omega),
    target.cyclic _ _⟩

def endpointF' : Set.Icc (base target) (upper target) :=
  ⟨(targetF' hm target).space, target.ordered _ _ (by simp only [Fin.le_def]; omega),
    target.cyclic _ _⟩

abbrev FiniteBounded (h : Bounds source target) :=
  BoundedGallery (base target) (upper target) (stable k _ _)
    (I0 h) (K0 h) (endpointF hm (target := target)) (endpointF' hm (target := target)) m (2*m+1)

private theorem quotient_node_dimension (T : Theory k (2*m+1))
    (Λ A : Lattice k (2*m+1)) (U : Submodule k (Ambient k (2*m+1)))
    (hΛU : Λ.space ≤ U) (hΛA : Λ.space ≤ A.space) (hAU : A.space ≤ U)
    (hΛ : degree k (2*m+1) Λ = 0) (d : ℕ) (hA : degree k (2*m+1) A = d) :
    Module.finrank k (quotientImage Λ.space U hΛU A.space hΛA hAU) = d := by
  rw [quotientImage_finrank]
  have h := T.dimension_degree Λ A hΛA
  rw [hΛ,hA,sub_zero] at h
  exact_mod_cast h

/-- Every actual six-gallery has precisely the quotient dimensions used in
 the finite gallery count. This uses only general lattice degree theory. -/
def Data.toBounded (T : Theory k (2*m+1)) (h : Bounds source target)
    (d : Data hm source target) : FiniteBounded hm h := by
  let g := d.toIncidence hm
  let b := incidenceEquivBounded (shift k (2*m+1)) (sourceNode source).space
    (targetNode target).space (targetF target).space (targetF' hm target).space g
  have hz : degree k (2*m+1) (targetNode target) = 0 := target.degree_eq _
  refine {
    toBoundedIncidence := b
    line_dim := ?_
    I_dim := ?_
    K_dim := ?_
    hyperplane_dim := ?_ }
  · exact quotient_node_dimension T _ d.L _ _
      (intermediate_bounds g).1.1 (intermediate_bounds g).1.2 hz 1 d.degree_L
  · exact quotient_node_dimension T _ d.I _ _
      (intermediate_bounds g).2.1.1 (intermediate_bounds g).2.1.2 hz m d.degree_I
  · apply quotient_node_dimension T _ d.K _ _
      (intermediate_bounds g).2.2.1.1 (intermediate_bounds g).2.2.1.2 hz (m+1)
    simpa using d.degree_K
  · apply quotient_node_dimension T _ d.H _ _
      (intermediate_bounds g).2.2.2.1 (intermediate_bounds g).2.2.2.2 hz (2*m+1-1)
    simpa using d.degree_H

def liftNode (T : Theory k (2*m+1))
    (A : Set.Icc (base target) (upper target)) : Lattice k (2*m+1) :=
  ((T.intervalIso (targetNode target)).symm A).val

@[simp] theorem liftNode_space (T : Theory k (2*m+1))
    (A : Set.Icc (base target) (upper target)) :
    (liftNode T A).space = A.val := by
  exact congrArg Subtype.val ((T.intervalIso (targetNode target)).apply_symm_apply A)

private theorem liftNode_degree (T : Theory k (2*m+1))
    (A : Set.Icc (base target) (upper target)) (d : ℕ)
    (hd : Module.finrank k ((quotientIntervalIso (base target) (upper target)
      (stable k _ _)).symm A) = d) :
    degree k (2*m+1) (liftNode T A) = d := by
  have hle : targetNode target ≤ liftNode T A := by
    change base target ≤ (liftNode T A).space
    rw [liftNode_space]
    exact A.property.1
  have h := T.dimension_degree (targetNode target) (liftNode T A) hle
  have hz : degree k (2*m+1) (targetNode target) = 0 := target.degree_eq _
  rw [hz,sub_zero,liftNode_space] at h
  have hq := quotientImage_finrank (base target) (upper target) (stable k _ _)
    A.val A.property.1 A.property.2
  change Module.finrank k ((quotientIntervalIso (base target) (upper target)
    (stable k _ _)).symm A) = _ at hq
  rw [← hq,hd] at h
  exact h.symm

/-- Lift the finite quotient gallery uniquely to actual full lattices.
Existence uses only the generic one-period lattice correspondence. -/
def Data.ofBounded (T : Theory k (2*m+1)) (h : Bounds source target)
    (b : FiniteBounded hm h) : Data hm source target where
  L := liftNode T b.L
  I := liftNode T b.I
  K := liftNode T b.K
  H := liftNode T b.H
  source_le_I := by
    change (sourceNode source).space ≤ (liftNode T b.I).space
    rw [liftNode_space]
    exact le_sup_left.trans b.I₀_le_I
  I_le_K := by
    change (liftNode T b.I).space ≤ (liftNode T b.K).space
    simpa only [liftNode_space] using b.I_le_K
  K_le_source_expand := by
    rw [liftNode_space]
    exact b.K_le_K₀.trans inf_le_left
  target_le_L := by
    change base target ≤ (liftNode T b.L).space
    rw [liftNode_space]
    exact b.L.property.1
  L_le_I := by
    change (liftNode T b.L).space ≤ (liftNode T b.I).space
    simpa only [liftNode_space] using b.L_le_I
  K_le_H := by
    change (liftNode T b.K).space ≤ (liftNode T b.H).space
    simpa only [liftNode_space] using b.K_le_H
  H_le_target_expand := by
    rw [liftNode_space]
    exact b.H.property.2
  L_le_F := by
    change (liftNode T b.L).space ≤ (targetF target).space
    simpa only [liftNode_space] using b.L_le_F
  F'_le_H := by
    change (targetF' hm target).space ≤ (liftNode T b.H).space
    simpa only [liftNode_space] using b.F'_le_H
  degree_L := liftNode_degree T b.L 1 b.line_dim
  degree_I := liftNode_degree T b.I m b.I_dim
  degree_K := by simpa using liftNode_degree T b.K (m+1) b.K_dim
  degree_H := by simpa using liftNode_degree T b.H (2*m+1-1) b.hyperplane_dim

/-- The four-lattice gallery and its actual finite quotient gallery are
isomorphic. The only inputs are the general lattice facts in `Theory`. -/
def dataBoundedEquiv (T : Theory k (2*m+1)) (h : Bounds source target) :
    Data hm source target ≃ FiniteBounded hm h where
  toFun := Data.toBounded hm T h
  invFun := Data.ofBounded hm T h
  left_inv d := by
    apply Data.ext
    all_goals apply Lattice.space_injective
    all_goals exact liftNode_space T _
  right_inv b := by
    apply LatticeGallery.boundedGallery_ext
    all_goals apply Subtype.ext
    all_goals exact liftNode_space T _

/-- The endpoint subspaces form the required interval. -/
theorem I0_le_K0 (h : Bounds source target) : (I0 h).val ≤ (K0 h).val :=
  sup_le (le_inf (stable k _ _) h.source_le)
    (le_inf h.target_le (stable k _ _))

theorem endpointF_le_endpointF' :
    (endpointF hm (target := target)).val ≤ (endpointF' hm (target := target)).val :=
  target.ordered _ _ (by simp only [Fin.le_def]; omega)

/-- The quotient target flag has dimensions m and m+1, derived from its
actual degree labels. -/
theorem quotient_endpoint_dimensions (T : Theory k (2*m+1)) :
    Module.finrank k ((quotientIntervalIso (base target) (upper target)
      (stable k _ _)).symm (endpointF hm (target := target))) = m ∧
    Module.finrank k ((quotientIntervalIso (base target) (upper target)
      (stable k _ _)).symm (endpointF' hm (target := target))) = m+1 := by
  constructor
  · exact quotient_node_dimension T _ (targetF target) _ _
      (endpointF hm).property.1 (endpointF hm).property.2
      (target.degree_eq _) m (target.degree_eq _)
  · apply quotient_node_dimension T _ (targetF' hm target) _ _
      (endpointF' hm).property.1 (endpointF' hm).property.2
      (target.degree_eq _) (m+1)
    simpa using (target.degree_eq
      ⟨⟨m+1,by omega⟩,(output_mem m _).mpr (Or.inr (Or.inr rfl))⟩)

/-- Exact finite-vector-space gallery for the original six partial flags. -/
def sixFiniteGalleryEquiv (T : Theory k (2*m+1)) (h : Bounds source target) :
    SixGallery source target ≃
      GalleryFlags.Gallery
        ((quotientIntervalIso (base target) (upper target) (stable k _ _)).symm (I0 h))
        ((quotientIntervalIso (base target) (upper target) (stable k _ _)).symm (K0 h))
        ((quotientIntervalIso (base target) (upper target) (stable k _ _)).symm (endpointF hm))
        ((quotientIntervalIso (base target) (upper target) (stable k _ _)).symm (endpointF' hm))
        m (2*m+1) :=
  (sixDataEquiv hm).trans ((dataBoundedEquiv hm T h).trans
    (boundedGalleryEquiv _ _ _ _ _ _ _ _ _))

end Guralnick.LatticeFlags.Family
