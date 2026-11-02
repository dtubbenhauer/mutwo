import Guralnick.AffineLatticePosition
import Guralnick.LatticeDegree
import Guralnick.FlagGallery

/-!
# Laurent-linear changes of coordinates on lattices and galleries

An actual invertible Laurent-linear map sends full power-series lattices to
full lattices. Relative quotients are naturally isomorphic, so the change of
signed degree is independent of the lattice. A map that preserves one degree
therefore transports all degree-normalized flags and their actual galleries.
-/
noncomputable section
namespace Guralnick.LatticeEquivariance
open LaurentLattice LatticeFlags AffineLatticePosition
variable {k : Type*} [Field k] {N : ℕ}

/-- Image of an actual full lattice under an actual Laurent-linear equivalence. -/
def mapLattice (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) (Λ : Lattice k N) :
    Lattice k N where
  module := mapModule k N g Λ.module
  finite := Λ.finite.map _
  spanning := by
    change Submodule.span (LaurentSeries k)
      (↑(Λ.module.map (g.restrictScalars (PowerSeries k)).toLinearMap) : Set (Ambient k N)) = ⊤
    rw [Submodule.map_coe]
    change Submodule.span (LaurentSeries k) (g '' (Λ.module : Set (Ambient k N))) = ⊤
    rw [← Submodule.map_span, Λ.spanning, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective

@[simp] theorem mapLattice_module (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (Λ : Lattice k N) : (mapLattice g Λ).module = mapModule k N g Λ.module := rfl

@[simp] theorem mapLattice_space (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (Λ : Lattice k N) :
    (mapLattice g Λ).space = Λ.space.map (g.restrictScalars k).toLinearMap := rfl

@[simp] theorem mapLattice_mem (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (Λ : Lattice k N) (x : Ambient k N) :
    g x ∈ (mapLattice g Λ).space ↔ x ∈ Λ.space := by
  change (∃ y, y ∈ Λ.space ∧ g y = g x) ↔ x ∈ Λ.space
  constructor
  · rintro ⟨y, hy, he⟩
    simpa only [g.injective he] using hy
  · intro hx
    exact ⟨x,hx,rfl⟩

@[simp] theorem mapLattice_symm_map (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (Λ : Lattice k N) : mapLattice g.symm (mapLattice g Λ) = Λ := by
  apply LaurentLattice.Lattice.ext
  ext x
  change (∃ y, (∃ z, z ∈ Λ.module ∧ g z = y) ∧ g.symm y = x) ↔ x ∈ Λ.module
  constructor
  · rintro ⟨y, ⟨z,hz,rfl⟩, he⟩
    simp only [g.symm_apply_apply] at he
    exact he ▸ hz
  · intro hx
    exact ⟨g x,⟨x,hx,rfl⟩,g.symm_apply_apply x⟩

@[simp] theorem mapLattice_map_symm (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (Λ : Lattice k N) : mapLattice g (mapLattice g.symm Λ) = Λ :=
  mapLattice_symm_map g.symm Λ

@[simp] theorem mapLattice_trans (g h : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (Λ : Lattice k N) : mapLattice (g.trans h) Λ = mapLattice h (mapLattice g Λ) := by
  apply LaurentLattice.Lattice.ext
  exact mapModule_trans k N g h Λ.module

/-- Coordinate changes preserve and reflect lattice inclusion. -/
def orderEquiv (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) :
    Lattice k N ≃o Lattice k N where
  toFun := mapLattice g
  invFun := mapLattice g.symm
  left_inv := mapLattice_symm_map g
  right_inv := mapLattice_map_symm g
  map_rel_iff' := by
    intro Λ M
    change Λ.module.map _ ≤ M.module.map _ ↔ Λ.module ≤ M.module
    exact Submodule.map_le_map_iff_of_injective (g.restrictScalars (PowerSeries k)).injective _ _

/-- The map on the vector space underlying an individual lattice. -/
def spaceEquiv (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) (M : Lattice k N) :
    M.space ≃ₗ[k] (mapLattice g M).space :=
  (g.restrictScalars k).ofSubmodules M.space (mapLattice g M).space rfl

@[simp] theorem spaceEquiv_apply (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (M : Lattice k N) (x : M.space) : (spaceEquiv g M x).val = g x.val := rfl

/-- A Laurent coordinate change preserves every vector-space subquotient. -/
def subspaceQuotientEquiv (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (A B : Submodule k (Ambient k N)) :
    LatticeGallery.QuotientSpace A B ≃ₗ[k]
      LatticeGallery.QuotientSpace (A.map (g.restrictScalars k).toLinearMap)
        (B.map (g.restrictScalars k).toLinearMap) := by
  let e := (g.restrictScalars k).submoduleMap B
  apply Submodule.Quotient.equiv _ _ e
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.val,hy,rfl⟩
  · rintro ⟨y,hy,he⟩
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    change (e.symm x).val ∈ A
    have he' : g (e.symm x).val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
    have hy' : y = (e.symm x).val := g.injective (he.trans he'.symm)
    exact hy' ▸ hy

/-- Relative quotient spaces, including nonnested pairs, are transported by g. -/
def quotientEquiv (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) (Λ M : Lattice k N) :
    LatticeGallery.QuotientSpace Λ.space M.space ≃ₗ[k]
      LatticeGallery.QuotientSpace (mapLattice g Λ).space (mapLattice g M).space :=
  subspaceQuotientEquiv g Λ.space M.space

theorem subspace_map_inf (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (A B : Submodule k (Ambient k N)) :
    (A ⊓ B).map (g.restrictScalars k).toLinearMap =
      A.map (g.restrictScalars k).toLinearMap ⊓ B.map (g.restrictScalars k).toLinearMap :=
  Submodule.map_inf _ g.injective

theorem subspace_map_sup (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (A B : Submodule k (Ambient k N)) :
    (A ⊔ B).map (g.restrictScalars k).toLinearMap =
      A.map (g.restrictScalars k).toLinearMap ⊔ B.map (g.restrictScalars k).toLinearMap :=
  Submodule.map_sup _ _ _

/-- The degree offset of g is the same at every full lattice. -/
theorem degree_difference (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (Λ M : Lattice k N) :
    degree k N (mapLattice g Λ) - degree k N Λ =
      degree k N (mapLattice g M) - degree k N M := by
  let I := interLattice Λ M
  have hIΛ : I ≤ Λ := interLattice_le_left Λ M
  have hIM : I ≤ M := interLattice_le_right Λ M
  have h₁ := dimension_degree I Λ hIΛ
  have h₂ := dimension_degree I M hIM
  have h₃ := dimension_degree (mapLattice g I) (mapLattice g Λ)
    ((orderEquiv g).monotone hIΛ)
  have h₄ := dimension_degree (mapLattice g I) (mapLattice g M)
    ((orderEquiv g).monotone hIM)
  have h₅ := congrArg (fun n : ℕ => (n : ℤ)) (quotientEquiv g I Λ).finrank_eq
  have h₆ := congrArg (fun n : ℕ => (n : ℤ)) (quotientEquiv g I M).finrank_eq
  dsimp only at h₅ h₆
  omega

/-- Normalizing one actual lattice fixes the degree offset everywhere. -/
theorem degree_preserving_of_one (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (M : Lattice k N) (hM : degree k N (mapLattice g M) = degree k N M) :
    ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ := by
  intro Λ
  have h := degree_difference g Λ M
  omega

/-- All Laurent-linear maps commute with multiplication by t⁻¹. -/
theorem map_shift (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) (x : Ambient k N) :
    g (shift k N x) = shift k N (g x) := by
  exact g.map_smul (HahnSeries.single (-1 : ℤ) (1 : k)) x

theorem map_expand (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (U : Submodule k (Ambient k N)) :
    (LatticeGallery.expand (shift k N) U).map (g.restrictScalars k).toLinearMap =
      LatticeGallery.expand (shift k N) (U.map (g.restrictScalars k).toLinearMap) := by
  unfold LatticeGallery.expand
  rw [← Submodule.map_comp,← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact map_shift g x

/-- The inverse coordinate change also preserves degree. -/
theorem degree_preserving_symm (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (hzero : ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ) :
    ∀ Λ, degree k N (mapLattice g.symm Λ) = degree k N Λ := by
  intro Λ
  have h := hzero (mapLattice g.symm Λ)
  rw [mapLattice_map_symm] at h
  exact h.symm

/-- An actual degree-preserving coordinate change acts on every retained mask. -/
def mapFlag (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (hzero : ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ)
    {S : Finset (Fin N)} (F : Flag k N S) : Flag k N S where
  node i := mapLattice g (F.node i)
  ordered i j hij := (orderEquiv g).monotone (F.ordered i j hij)
  cyclic i j := by
    rw [mapLattice_space,mapLattice_space,← map_expand]
    exact Submodule.map_mono (F.cyclic i j)
  degree_eq i := (hzero _).trans (F.degree_eq i)

/-- The flag action is an equivalence, not only a map on numerical invariants. -/
def flagEquiv (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (hzero : ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ)
    {S : Finset (Fin N)} : Flag k N S ≃ Flag k N S where
  toFun := mapFlag g hzero
  invFun := mapFlag g.symm (degree_preserving_symm g hzero)
  left_inv F := by
    apply LatticeFlags.Flag.ext
    funext i
    exact mapLattice_symm_map g (F.node i)
  right_inv F := by
    apply LatticeFlags.Flag.ext
    funext i
    exact mapLattice_map_symm g (F.node i)

@[simp] theorem flagEquiv_node (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (hzero : ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ)
    {S : Finset (Fin N)} (F : Flag k N S) (i : {i // i ∈ S}) :
    (flagEquiv g hzero F).node i = mapLattice g (F.node i) := rfl

@[simp] theorem compatible_flagEquiv_iff
    (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (hzero : ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ)
    {S T : Finset (Fin N)} (F : Flag k N S) (G : Flag k N T) :
    Compatible (flagEquiv g hzero F) (flagEquiv g hzero G) ↔ Compatible F G := by
  constructor
  · intro h i hi hj
    exact (orderEquiv g).injective (h i hi hj)
  · intro h i hi hj
    exact congrArg (mapLattice g) (h i hi hj)

end Guralnick.LatticeEquivariance

namespace Guralnick.LatticeEquivariance
open LaurentLattice LatticeFlags CanonicalChains ParabolicWeb
variable {k : Type} [Field k] {N : ℕ}

/-- The actual common-refinement fibers are preserved. -/
def refinementEquiv (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (hzero : ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ)
    {I J : Index N} (F : Flag k N (retained I)) (G : Flag k N (retained J)) :
    FlagConvolution.Refinement k F G ≃
      FlagConvolution.Refinement k (flagEquiv g hzero F) (flagEquiv g hzero G) :=
  (flagEquiv g hzero).subtypeEquiv (fun R => by
    simp only [compatible_flagEquiv_iff])

/-- A coordinate change transports the complete gallery, including every
intermediate flag and common refinement in an arbitrary chain. -/
def galleryEquiv (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (hzero : ∀ Λ, degree k N (mapLattice g Λ) = degree k N Λ) :
    {I J : Index N} → (path : Chain I J) →
      (source : Flag k N (retained I)) → (target : Flag k N (retained J)) →
      FlagConvolution.Gallery k path source target ≃
        FlagConvolution.Gallery k path (flagEquiv g hzero source) (flagEquiv g hzero target)
  | _,_,.nil _,source,target => by
    simp only [FlagConvolution.Gallery]
    exact {
      toFun := fun h => ⟨congrArg (flagEquiv g hzero) h.down⟩
      invFun := fun h => ⟨(flagEquiv g hzero).injective h.down⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  | _,_,.snoc path _,source,target => by
    simp only [FlagConvolution.Gallery]
    exact Equiv.sigmaCongr (flagEquiv g hzero) (fun middle =>
      Equiv.prodCongr (galleryEquiv g hzero path source middle)
        (refinementEquiv g hzero middle target))

#print axioms subspaceQuotientEquiv
#print axioms degree_difference
#print axioms flagEquiv
#print axioms galleryEquiv
end Guralnick.LatticeEquivariance
