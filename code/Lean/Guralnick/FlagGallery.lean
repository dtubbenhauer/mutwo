import Guralnick.CanonicalChains
import Guralnick.AffineLatticePosition
import Guralnick.LatticeTheory
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Actual galleries and their finiteness over finite coefficient fields.
No Hecke/convolution coefficient is used to define or bound a gallery. -/
noncomputable section
namespace Guralnick.FlagConvolution
open Hecke ParabolicWeb CanonicalChains LatticeFlags LaurentLattice
variable {n : ℕ} (k : Type) [Field k]

/-- Actual flag choices, including the common-facet refinement at each step. -/
def Gallery : {I J : Index n} → (path : Chain I J) →
    Flag k n (retained I) → Flag k n (retained J) → Type
  | _, _, .nil _, source, target => PLift (source = target)
  | _, _, .snoc (J := J) path T, source, target =>
      (middle : Flag k n (retained J)) ×
        Gallery path source middle ×
          {refinement : Flag k n (retained (meet J T)) //
            Compatible middle refinement ∧ Compatible refinement target}

/-- Actual full lattices between two specified bounds. -/
def BoundedLattices (Λ M : Lattice k n) := {L : Lattice k n // Λ ≤ L ∧ L ≤ M}

/-- The finite quotient correspondence bounds the number of actual lattices. -/
theorem boundedLattices_finite [Finite k] (Λ M : Lattice k n) (hΛM : Λ ≤ M) :
    Finite (BoundedLattices k Λ M) := by
  letI : FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space M.space) :=
    LaurentLattice.finite_quotient Λ M hΛM
  letI : Finite (LatticeGallery.QuotientSpace Λ.space M.space) := Module.finite_of_finite k
  letI : Finite (Submodule k (LatticeGallery.QuotientSpace Λ.space M.space)) :=
    Finite.of_injective (fun U : Submodule k (LatticeGallery.QuotientSpace Λ.space M.space) =>
      (U : Set (LatticeGallery.QuotientSpace Λ.space M.space))) SetLike.coe_injective
  let e := LatticeGallery.quotientIntervalIso Λ.space M.space hΛM
  letI : Finite (Set.Icc Λ.space M.space) := Finite.of_injective e.symm e.symm.injective
  apply Finite.of_injective
    (fun L : BoundedLattices k Λ M => (⟨L.val.space,L.property⟩ : Set.Icc Λ.space M.space))
  intro L L' h
  apply Subtype.ext
  exact Lattice.space_injective (congrArg Subtype.val h)

/-- One expansion is injective on actual lattices. -/
theorem periodTower_one_injective : Function.Injective (fun Λ : Lattice k n => periodTower Λ 1) := by
  intro Λ M h
  apply Lattice.space_injective
  have he := congrArg Lattice.space h
  change Λ.space.map (shift k n).toLinearMap = M.space.map (shift k n).toLinearMap at he
  exact Submodule.map_injective_of_injective (shift k n).injective he

theorem retained_nonempty (I : Index n) : (retained I).Nonempty := by
  classical
  by_contra h
  apply I.property
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  exact h ⟨i, by simpa [retained] using hi⟩

theorem retained_meet (I J : Index n) : retained (meet I J) = retained I ∪ retained J := by
  ext i
  simp only [retained,meet,Finset.mem_compl,Finset.mem_inter,Finset.mem_union]
  tauto

def Refinement {I J : Index n} (F : Flag k n (retained I)) (G : Flag k n (retained J)) :=
  {R : Flag k n (retained (meet I J)) // Compatible F R ∧ Compatible R G}

/-- The common refinement retains exactly the union of the two boundaries,
so its lattices are forced whenever it exists. -/
instance refinement_subsingleton {I J : Index n}
    (F : Flag k n (retained I)) (G : Flag k n (retained J)) :
    Subsingleton (Refinement k F G) := by
  refine ⟨?_⟩
  intro R R'
  apply Subtype.ext
  apply LatticeFlags.Flag.ext
  funext i
  have hi : i.val ∈ retained I ∪ retained J := by
    rw [← retained_meet]
    exact i.property
  rcases Finset.mem_union.mp hi with hi | hi
  · exact (R.property.1 i.val hi i.property).symm.trans
      (R'.property.1 i.val hi i.property)
  · exact (R.property.2 i.val i.property hi).trans
      (R'.property.2 i.val i.property hi).symm

/-- Compatibility through a common refinement bounds every middle node
by the two periods around any chosen target node. -/
theorem refinement_node_bounds {I J : Index n}
    (F : Flag k n (retained I)) (G : Flag k n (retained J))
    (R : Refinement k F G) (i : {i // i ∈ retained I}) (a : {i // i ∈ retained J}) :
    G.node a ≤ periodTower (F.node i) 1 ∧
      periodTower (F.node i) 1 ≤ periodTower (G.node a) 2 := by
  have hi : i.val ∈ retained (meet I J) := by
    rw [retained_meet]
    exact Finset.mem_union_left _ i.property
  have ha : a.val ∈ retained (meet I J) := by
    rw [retained_meet]
    exact Finset.mem_union_right _ a.property
  have h₁ := R.val.cyclic ⟨a.val,ha⟩ ⟨i.val,hi⟩
  have h₂ := R.val.cyclic ⟨i.val,hi⟩ ⟨a.val,ha⟩
  rw [R.property.2 a.val ha a.property, ← R.property.1 i.val i.property hi] at h₁ h₂
  refine ⟨h₁,?_⟩
  change (F.node i).space.map (shift k n).toLinearMap ≤
    ((G.node a).space.map (shift k n).toLinearMap).map (shift k n).toLinearMap
  exact Submodule.map_mono h₂

def PossibleMiddle (I J : Index n) (G : Flag k n (retained J)) :=
  {F : Flag k n (retained I) // Nonempty (Refinement k F G)}

/-- For a fixed target there are finitely many possible previous flags;
all their expanded nodes lie in one fixed finite lattice interval. -/
theorem possibleMiddle_finite [Finite k] (I J : Index n) (G : Flag k n (retained J)) :
    Finite (PossibleMiddle k I J G) := by
  classical
  obtain ⟨a,ha⟩ := retained_nonempty J
  let Λ := G.node ⟨a,ha⟩
  let U := periodTower Λ 2
  letI : Finite (BoundedLattices k Λ U) := boundedLattices_finite k Λ U (le_periodTower Λ 2)
  let f : PossibleMiddle k I J G → ({i // i ∈ retained I} → BoundedLattices k Λ U) :=
    fun F i => ⟨periodTower (F.val.node i) 1,
      refinement_node_bounds k F.val G (Classical.choice F.property) i ⟨a,ha⟩⟩
  apply Finite.of_injective f
  intro F F' h
  apply Subtype.ext
  apply LatticeFlags.Flag.ext
  funext i
  apply periodTower_one_injective k
  exact congrArg Subtype.val (congrFun h i)

/-- Reindexing the last step by its possible middle flags removes the
otherwise infinite ambient flag index. -/
def gallerySnocEquiv {I J : Index n} (path : Chain I J) (T : Index n)
    (source : Flag k n (retained I)) (target : Flag k n (retained T)) :
    Gallery k (.snoc path T) source target ≃
      ((middle : PossibleMiddle k J T target) ×
        Gallery k path source middle.val × Refinement k middle.val target) := by
  let e : ((middle : Flag k n (retained J)) ×
      Gallery k path source middle × Refinement k middle target) ≃
      ((middle : PossibleMiddle k J T target) ×
        Gallery k path source middle.val × Refinement k middle.val target) := {
    toFun g := ⟨⟨g.1,⟨g.2.2⟩⟩,g.2.1,g.2.2⟩
    invFun g := ⟨g.1.val,g.2.1,g.2.2⟩
    left_inv g := rfl
    right_inv g := by cases g; rfl }
  exact (Equiv.cast (by simp only [Gallery,Refinement])).trans e

/-- Finiteness of every actual finite-chain gallery over a finite field,
proved from lattice incidence alone. -/
theorem gallery_finite [Finite k] {I J : Index n} (path : Chain I J)
    (source : Flag k n (retained I)) (target : Flag k n (retained J)) :
    Finite (Gallery k path source target) := by
  induction path generalizing source with
  | nil =>
      simp only [Gallery]
      infer_instance
  | @snoc J path T ih =>
      letI : Finite (PossibleMiddle k J T target) := possibleMiddle_finite k J T target
      letI : ∀ middle : PossibleMiddle k J T target,
          Finite (Gallery k path source middle.val) := fun middle => ih source middle.val
      exact Finite.of_injective (gallerySnocEquiv k path T source target)
        (gallerySnocEquiv k path T source target).injective

#print axioms gallery_finite
end Guralnick.FlagConvolution
