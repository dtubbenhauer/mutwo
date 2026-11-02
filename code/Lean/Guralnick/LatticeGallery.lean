import Guralnick.GalleryFlags
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Interval.Set.OrderIso

/-!
# Lattice incidence and passage to the endpoint quotient

The ambient space is a genuine vector space with an invertible linear
operator T, standing for multiplication by t⁻¹. We record stable periodic
subspaces explicitly. Realizing them as full Laurent-series lattices and
identifying their relative matrices is a separate step.

The incidence implications and quotient correspondence below are proved,
not assumed. Equal determinant degree is a separate dimension comparison;
it must not be inferred solely from the incidence conditions.
-/

namespace Guralnick.LatticeGallery
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The expansion of a subspace under multiplication by t⁻¹. -/
def expand (T : V ≃ₗ[k] V) (Λ : Submodule k V) : Submodule k V :=
  Λ.map T.toLinearMap

/-- The stability condition for a lattice, viewed as a k-subspace.
Freeness/discreteness over k[[t]] is not part of this elementary structure. -/
structure PeriodicSubspace (T : V ≃ₗ[k] V) where
  space : Submodule k V
  stable : space ≤ expand T space

/-- The ambient lattice-gallery incidences before taking a quotient or
asserting any dimension count. -/
structure Incidence (T : V ≃ₗ[k] V) (Λ Λ' F F' : Submodule k V) where
  L : Submodule k V
  I : Submodule k V
  K : Submodule k V
  H : Submodule k V
  source_le_I : Λ ≤ I
  I_le_K : I ≤ K
  K_le_source_expand : K ≤ expand T Λ
  target_le_L : Λ' ≤ L
  L_le_I : L ≤ I
  K_le_H : K ≤ H
  H_le_target_expand : H ≤ expand T Λ'
  L_le_F : L ≤ F
  F'_le_H : F' ≤ H

/-- A gallery forces relative lattice displacement at most one in both
 directions. This is the containment input to three-column support. -/
theorem endpoint_bounds {T : V ≃ₗ[k] V} {Λ Λ' F F' : Submodule k V}
    (g : Incidence T Λ Λ' F F') :
    Λ ≤ expand T Λ' ∧ Λ' ≤ expand T Λ := by
  constructor
  · exact g.source_le_I.trans (g.I_le_K.trans
      (g.K_le_H.trans g.H_le_target_expand))
  · exact g.target_le_L.trans (g.L_le_I.trans
      (g.I_le_K.trans g.K_le_source_expand))

/-- Every intermediate lattice belongs to the target quotient interval. -/
theorem intermediate_bounds {T : V ≃ₗ[k] V} {Λ Λ' F F' : Submodule k V}
    (g : Incidence T Λ Λ' F F') :
    (Λ' ≤ g.L ∧ g.L ≤ expand T Λ') ∧
    (Λ' ≤ g.I ∧ g.I ≤ expand T Λ') ∧
    (Λ' ≤ g.K ∧ g.K ≤ expand T Λ') ∧
    (Λ' ≤ g.H ∧ g.H ≤ expand T Λ') := by
  have hI := g.I_le_K.trans (g.K_le_H.trans g.H_le_target_expand)
  have hK := g.K_le_H.trans g.H_le_target_expand
  exact ⟨⟨g.target_le_L,g.L_le_I.trans hI⟩,
    ⟨g.target_le_L.trans g.L_le_I,hI⟩,
    ⟨g.target_le_L.trans (g.L_le_I.trans g.I_le_K),hK⟩,
    ⟨g.target_le_L.trans (g.L_le_I.trans (g.I_le_K.trans g.K_le_H)),
      g.H_le_target_expand⟩⟩

/-- The actual endpoint quotient `(U)/(B)`, using B as a subspace of U. -/
abbrev QuotientSpace (B U : Submodule k V) := U ⧸ B.comap U.subtype

private def nestedIntervalIso (B U : Submodule k V) (hBU : B ≤ U) :
    Set.Ici (⟨B,hBU⟩ : Set.Iic U) ≃o Set.Icc B U where
  toFun a := ⟨a.val.val, a.property, a.val.property⟩
  invFun a := ⟨⟨a.val,a.property.2⟩,a.property.1⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl
  map_rel_iff' := Iff.rfl

/-- The correspondence theorem identifies all subspaces of the actual
quotient with exactly the intermediate ambient subspaces. -/
def quotientIntervalIso (B U : Submodule k V) (hBU : B ≤ U) :
    Submodule k (QuotientSpace B U) ≃o Set.Icc B U := by
  let S : Submodule k U ≃o Set.Iic U := Submodule.MapSubtype.orderIso U
  let B' : Submodule k U := B.comap U.subtype
  have hbase : S B' = (⟨B,hBU⟩ : Set.Iic U) := by
    apply Subtype.ext
    change (B.comap U.subtype).map U.subtype = B
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hBU]
  exact ((Submodule.comapMkQRelIso B').trans (S.Ici B')).trans
    ((OrderIso.setCongr (Set.Ici (S B')) (Set.Ici (⟨B,hBU⟩ : Set.Iic U))
      (congrArg (fun A : Set.Iic U => Set.Ici A) hbase)).trans
      (nestedIntervalIso B U hBU))

/-- The quotient-space image of an actual intermediate subspace. -/
def quotientImage (B U : Submodule k V) (hBU : B ≤ U)
    (A : Submodule k V) (hBA : B ≤ A) (hAU : A ≤ U) :
    Submodule k (QuotientSpace B U) :=
  (quotientIntervalIso B U hBU).symm ⟨A,hBA,hAU⟩

/-- Passing to the quotient preserves and reflects every containment. -/
theorem quotientImage_le_iff (B U : Submodule k V) (hBU : B ≤ U)
    (A C : Submodule k V) (hBA : B ≤ A) (hAU : A ≤ U)
    (hBC : B ≤ C) (hCU : C ≤ U) :
    quotientImage B U hBU A hBA hAU ≤ quotientImage B U hBU C hBC hCU ↔ A ≤ C :=
  (quotientIntervalIso B U hBU).symm.le_iff_le

/-- Incidence data with all four intermediate subspaces recorded in the
actual endpoint interval. The endpoint data are still ambient subspaces. -/
structure BoundedIncidence (B U I₀ K₀ F F' : Submodule k V) where
  L : Set.Icc B U
  I : Set.Icc B U
  K : Set.Icc B U
  H : Set.Icc B U
  L_le_I : L.val ≤ I.val
  I_le_K : I.val ≤ K.val
  K_le_H : K.val ≤ H.val
  L_le_F : L.val ≤ F
  F'_le_H : F' ≤ H.val
  I₀_le_I : I₀ ≤ I.val
  K_le_K₀ : K.val ≤ K₀

/-- This is the original lattice-incidence change of variables
`I₀=Λ+Λ'` and `K₀=TΛ∩TΛ'`, proved in both directions. -/
def incidenceEquivBounded (T : V ≃ₗ[k] V) (Λ Λ' F F' : Submodule k V) :
    Incidence T Λ Λ' F F' ≃
      BoundedIncidence Λ' (expand T Λ') (Λ ⊔ Λ')
        (expand T Λ ⊓ expand T Λ') F F' where
  toFun g :=
    { L := ⟨g.L,(intermediate_bounds g).1⟩
      I := ⟨g.I,(intermediate_bounds g).2.1⟩
      K := ⟨g.K,(intermediate_bounds g).2.2.1⟩
      H := ⟨g.H,(intermediate_bounds g).2.2.2⟩
      L_le_I := g.L_le_I
      I_le_K := g.I_le_K
      K_le_H := g.K_le_H
      L_le_F := g.L_le_F
      F'_le_H := g.F'_le_H
      I₀_le_I := sup_le g.source_le_I (g.target_le_L.trans g.L_le_I)
      K_le_K₀ := le_inf g.K_le_source_expand
        (g.K_le_H.trans g.H_le_target_expand) }
  invFun g :=
    { L := g.L.val
      I := g.I.val
      K := g.K.val
      H := g.H.val
      source_le_I := le_sup_left.trans g.I₀_le_I
      I_le_K := g.I_le_K
      K_le_source_expand := g.K_le_K₀.trans inf_le_left
      target_le_L := g.L.property.1
      L_le_I := g.L_le_I
      K_le_H := g.K_le_H
      H_le_target_expand := g.H.property.2
      L_le_F := g.L_le_F
      F'_le_H := g.F'_le_H }
  left_inv g := by cases g; rfl
  right_inv g := by cases g; rfl

/-- Once the target-quotient dimensions are known, all remaining data can
be transported through the quotient order isomorphism. This definition
intentionally does not assert the equal-determinant dimension comparison. -/
structure BoundedGallery (B U : Submodule k V) (hBU : B ≤ U)
    (I₀ K₀ F F' : Set.Icc B U) (m N : ℕ)
    extends BoundedIncidence B U I₀.val K₀.val F.val F'.val where
  line_dim : Module.finrank k ((quotientIntervalIso B U hBU).symm L) = 1
  I_dim : Module.finrank k ((quotientIntervalIso B U hBU).symm I) = m
  K_dim : Module.finrank k ((quotientIntervalIso B U hBU).symm K) = m+1
  hyperplane_dim : Module.finrank k ((quotientIntervalIso B U hBU).symm H) = N-1

theorem boundedGallery_ext {B U : Submodule k V} {hBU : B ≤ U}
    {I₀ K₀ F F' : Set.Icc B U} {m N : ℕ}
    {g h : BoundedGallery B U hBU I₀ K₀ F F' m N}
    (hL : g.L = h.L) (hI : g.I = h.I) (hK : g.K = h.K) (hH : g.H = h.H) :
    g = h := by
  cases g with
  | mk g₀ gl gi gk gh =>
    cases h with
    | mk h₀ hl hi hk hh =>
      cases g₀
      cases h₀
      cases hL
      cases hI
      cases hK
      cases hH
      rfl

private theorem finiteGallery_ext {E : Type*} [AddCommGroup E] [Module k E]
    {I₀ K₀ F F' : Submodule k E} {m N : ℕ}
    {g h : GalleryFlags.Gallery I₀ K₀ F F' m N}
    (hL : g.L = h.L) (hI : g.I = h.I) (hK : g.K = h.K) (hH : g.H = h.H) :
    g = h := by
  cases g
  cases h
  cases hL
  cases hI
  cases hK
  cases hH
  rfl

/-- An explicit equivalence with the finite-vector-space gallery used by
`GalleryFlags.galleryEquiv`. Every subspace and incidence is transported;
no extra lattice choices are forgotten. -/
def boundedGalleryEquiv (B U : Submodule k V) (hBU : B ≤ U)
    (I₀ K₀ F F' : Set.Icc B U) (m N : ℕ) :
    BoundedGallery B U hBU I₀ K₀ F F' m N ≃
      GalleryFlags.Gallery
        ((quotientIntervalIso B U hBU).symm I₀)
        ((quotientIntervalIso B U hBU).symm K₀)
        ((quotientIntervalIso B U hBU).symm F)
        ((quotientIntervalIso B U hBU).symm F') m N := by
  let e := quotientIntervalIso B U hBU
  refine
    { toFun := fun g =>
        { L := e.symm g.L
          I := e.symm g.I
          K := e.symm g.K
          H := e.symm g.H
          line_dim := g.line_dim
          I_dim := g.I_dim
          K_dim := g.K_dim
          hyperplane_dim := g.hyperplane_dim
          line_le_I := e.symm.monotone g.L_le_I
          I_le_K := e.symm.monotone g.I_le_K
          K_le_H := e.symm.monotone g.K_le_H
          line_le_F := e.symm.monotone g.L_le_F
          F'_le_H := e.symm.monotone g.F'_le_H
          I₀_le_I := e.symm.monotone g.I₀_le_I
          K_le_K₀ := e.symm.monotone g.K_le_K₀ }
      invFun := fun g =>
        { L := e g.L
          I := e g.I
          K := e g.K
          H := e g.H
          L_le_I := e.monotone g.line_le_I
          I_le_K := e.monotone g.I_le_K
          K_le_H := e.monotone g.K_le_H
          L_le_F := ?_
          F'_le_H := ?_
          I₀_le_I := ?_
          K_le_K₀ := ?_
          line_dim := ?_
          I_dim := ?_
          K_dim := ?_
          hyperplane_dim := ?_ }
      left_inv := ?_
      right_inv := ?_ }
  · have h := e.monotone g.line_le_F
    simpa only [e, OrderIso.apply_symm_apply] using h
  · have h := e.monotone g.F'_le_H
    simpa only [e, OrderIso.apply_symm_apply] using h
  · have h := e.monotone g.I₀_le_I
    simpa only [e, OrderIso.apply_symm_apply] using h
  · have h := e.monotone g.K_le_K₀
    simpa only [e, OrderIso.apply_symm_apply] using h
  · exact (congrArg (fun S : Submodule k (QuotientSpace B U) => Module.finrank k S)
      (e.symm_apply_apply g.L)).trans g.line_dim
  · exact (congrArg (fun S : Submodule k (QuotientSpace B U) => Module.finrank k S)
      (e.symm_apply_apply g.I)).trans g.I_dim
  · exact (congrArg (fun S : Submodule k (QuotientSpace B U) => Module.finrank k S)
      (e.symm_apply_apply g.K)).trans g.K_dim
  · exact (congrArg (fun S : Submodule k (QuotientSpace B U) => Module.finrank k S)
      (e.symm_apply_apply g.H)).trans g.hyperplane_dim
  · intro g
    exact boundedGallery_ext (e.apply_symm_apply g.L) (e.apply_symm_apply g.I)
      (e.apply_symm_apply g.K) (e.apply_symm_apply g.H)
  · intro g
    exact finiteGallery_ext (e.symm_apply_apply g.L) (e.symm_apply_apply g.I)
      (e.symm_apply_apply g.K) (e.symm_apply_apply g.H)

end Guralnick.LatticeGallery
