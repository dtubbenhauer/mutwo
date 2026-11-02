import Guralnick.PolynomialAffineCoordinates
import Guralnick.FlagGallery

/-!
# Independent polynomial flags and the full completion comparison

The polynomial flag uses actual Laurent-polynomial lattices, their own
signed degree, and their actual Laurent shift. Completion preserves all
three conditions and gives an equivalence for arbitrary cyclic masks.
The equivalence also preserves each intermediate flag and common-facet
refinement in the gallery used by the web calculation.
-/
noncomputable section
namespace Guralnick.PolynomialFlags
open PolynomialLattice
variable (k : Type) [Field k] (N : ℕ)

structure Flag (S : Finset (Fin N)) where
  node : {i // i ∈ S} → Lattice k N
  ordered : ∀ i j, i.val ≤ j.val → node i ≤ node j
  cyclic : ∀ i j, (node i).space ≤ LatticeGallery.expand (shift k N) (node j).space
  degree_eq : ∀ i, degree (node i) = (i.val.val : ℤ)

variable {k N}
@[ext] theorem Flag.ext {S : Finset (Fin N)} {F G : Flag k N S}
    (h : F.node = G.node) : F = G := by cases F; cases G; cases h; rfl

def Compatible {S T : Finset (Fin N)} (F : Flag k N S) (G : Flag k N T) : Prop :=
  ∀ (i : Fin N) (hi : i ∈ S) (hj : i ∈ T), F.node ⟨i,hi⟩ = G.node ⟨i,hj⟩

/-- Natural completion of every node, with absolute degrees unchanged. -/
def completeFlag {S : Finset (Fin N)} (F : Flag k N S) : LatticeFlags.Flag k N S where
  node i := LatticeCompletion.complete (F.node i)
  ordered i j hij := LatticeCompletion.orderIso.monotone (F.ordered i j hij)
  cyclic i j := (LatticeCompletion.complete_cyclic_iff (F.node i) (F.node j)).mpr (F.cyclic i j)
  degree_eq i := (LatticeCompletion.complete_degree (F.node i)).trans (F.degree_eq i)

/-- Algebraization takes the actual inverse-image lattice at each node. -/
def algebraizeFlag {S : Finset (Fin N)} (F : LatticeFlags.Flag k N S) : Flag k N S where
  node i := LatticeCompletion.algebraize (F.node i)
  ordered i j hij := LatticeCompletion.orderIso.symm.monotone (F.ordered i j hij)
  cyclic i j := by
    apply (LatticeCompletion.complete_cyclic_iff _ _).mp
    simpa only [LatticeCompletion.complete_algebraize] using F.cyclic i j
  degree_eq i := by
    have h := LatticeCompletion.complete_degree (LatticeCompletion.algebraize (F.node i))
    rw [LatticeCompletion.complete_algebraize,F.degree_eq] at h
    exact h.symm

@[simp] theorem algebraize_completeFlag {S : Finset (Fin N)} (F : Flag k N S) :
    algebraizeFlag (completeFlag F) = F := by
  apply Flag.ext
  funext i
  exact LatticeCompletion.algebraize_complete (F.node i)

@[simp] theorem complete_algebraizeFlag {S : Finset (Fin N)} (F : LatticeFlags.Flag k N S) :
    completeFlag (algebraizeFlag F) = F := by
  apply LatticeFlags.Flag.ext
  funext i
  exact LatticeCompletion.complete_algebraize (F.node i)

/-- Global flag equivalence for every retained cyclic mask. -/
def flagEquiv (S : Finset (Fin N)) : Flag k N S ≃ LatticeFlags.Flag k N S where
  toFun := completeFlag
  invFun := algebraizeFlag
  left_inv := algebraize_completeFlag
  right_inv := complete_algebraizeFlag

theorem compatible_iff {S T : Finset (Fin N)} (F : Flag k N S) (G : Flag k N T) :
    LatticeFlags.Compatible (completeFlag F) (completeFlag G) ↔ Compatible F G := by
  constructor
  · intro h i hi hj
    exact LatticeCompletion.orderIso.injective (h i hi hj)
  · intro h i hi hj
    exact congrArg LatticeCompletion.complete (h i hi hj)

/-- Forgetting retained nodes commutes with completion. -/
def Flag.restrict {S T : Finset (Fin N)} (F : Flag k N S) (h : T ⊆ S) : Flag k N T where
  node i := F.node ⟨i.val,h i.property⟩
  ordered i j hij := F.ordered _ _ hij
  cyclic i j := F.cyclic _ _
  degree_eq i := F.degree_eq _

@[simp] theorem complete_restrict {S T : Finset (Fin N)} (F : Flag k N S) (h : T ⊆ S) :
    completeFlag (F.restrict h) = (completeFlag F).restrict h := rfl

open ParabolicWeb CanonicalChains LatticeFlags in
/-- The exact same gallery construction in the independent polynomial model. -/
def Gallery : {I J : Index N} → (path : Chain I J) →
    Flag k N (retained I) → Flag k N (retained J) → Type
  | _, _, .nil _, source, target => PLift (source = target)
  | _, _, .snoc (J := J) path T, source, target =>
      (middle : Flag k N (retained J)) ×
        Gallery path source middle ×
          {refinement : Flag k N (retained (meet J T)) //
            Compatible middle refinement ∧ Compatible refinement target}

open ParabolicWeb CanonicalChains LatticeFlags

def refinementEquiv {I J : Index N} (F : Flag k N (retained I)) (G : Flag k N (retained J)) :
    {R : Flag k N (retained (meet I J)) // Compatible F R ∧ Compatible R G} ≃
      FlagConvolution.Refinement k (completeFlag F) (completeFlag G) where
  toFun R := ⟨completeFlag R.val,(compatible_iff F R.val).mpr R.property.1,
    (compatible_iff R.val G).mpr R.property.2⟩
  invFun R := ⟨algebraizeFlag R.val,by
    constructor
    · apply (compatible_iff F _).mp
      simpa only [complete_algebraizeFlag] using R.property.1
    · apply (compatible_iff _ G).mp
      simpa only [complete_algebraizeFlag] using R.property.2⟩
  left_inv R := by apply Subtype.ext; exact algebraize_completeFlag R.val
  right_inv R := by apply Subtype.ext; exact complete_algebraizeFlag R.val

/-- Every individual gallery, including its common-facet choices, is
transported bijectively. This is not a comparison of counts alone. -/
def galleryEquiv : {I J : Index N} → (path : Chain I J) →
    (source : Flag k N (retained I)) → (target : Flag k N (retained J)) →
    Gallery path source target ≃
      FlagConvolution.Gallery k path (completeFlag source) (completeFlag target)
  | _, _, .nil I, source, target => by
      simp only [Gallery,FlagConvolution.Gallery]
      exact {
        toFun := fun h => ⟨congrArg completeFlag h.down⟩
        invFun := fun h => ⟨(flagEquiv (retained I)).injective h.down⟩
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  | _, _, .snoc (J := J) path T, source, target => by
      simp only [Gallery,FlagConvolution.Gallery]
      refine Equiv.sigmaCongr (flagEquiv (retained J)) fun middle => ?_
      exact (galleryEquiv path source middle).prodCongr (refinementEquiv middle target)

theorem gallery_card {I J : Index N} (path : Chain I J)
    (source : Flag k N (retained I)) (target : Flag k N (retained J)) :
    Nat.card (Gallery path source target) =
      Nat.card (FlagConvolution.Gallery k path (completeFlag source) (completeFlag target)) :=
  Nat.card_congr (galleryEquiv path source target)

theorem gallery_finite [Finite k] {I J : Index N} (path : Chain I J)
    (source : Flag k N (retained I)) (target : Flag k N (retained J)) :
    Finite (Gallery path source target) := by
  letI := FlagConvolution.gallery_finite k path (completeFlag source) (completeFlag target)
  exact Finite.of_injective (galleryEquiv path source target) (galleryEquiv path source target).injective

#print axioms flagEquiv
#print axioms galleryEquiv
end Guralnick.PolynomialFlags
