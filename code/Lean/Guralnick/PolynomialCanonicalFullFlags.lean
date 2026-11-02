import Guralnick.FullFlagHeckeConvolution

/-! # Literal full coordinate lifts of canonical endpoint pairs

The full flags retain every degree and the same affine window. Forgetting
vertices gives the originally specified canonical partial pair exactly.
-/
noncomputable section
namespace Guralnick.PolynomialCanonicalFullFlags
open Hecke ParabolicWeb PolynomialFullGallery PolynomialFlags
variable {k : Type} [Field k] {n : ℕ} [NeZero n]

abbrev target : FullFlag k n :=
  PolynomialCoordinateFlags.target k n (LatticeFlags.retained (fullIndex n))

abbrev source (c : WindowCoxeter n) (w : AffinePermutation n) : FullFlag k n :=
  PolynomialCoordinateFlags.source k n c w (LatticeFlags.retained (fullIndex n))

theorem relativePosition (c : WindowCoxeter n) (w : AffinePermutation n) :
    FullFlagHeckeConvolution.RelativePosition (target (k := k)) (source c w) w := by
  refine ⟨LinearEquiv.refl _ _,?_,?_⟩
  · intro i
    rw [PolynomialCoordinateFlags.target_node_module]
    change Submodule.map (LinearMap.id : PolynomialLattice.Ambient k n →ₗ[Polynomial k] _) _ = _
    exact Submodule.map_id _
  · intro i
    rw [PolynomialCoordinateFlags.source_node_module]
    change Submodule.map (LinearMap.id : PolynomialLattice.Ambient k n →ₗ[Polynomial k] _) _ = _
    exact Submodule.map_id _

theorem forget_pair {I J : Index n}
    (c : WindowCoxeter n) (w : AffinePermutation n)
    (S : PolynomialFlags.Flag k n (LatticeFlags.retained I))
    (T : PolynomialFlags.Flag k n (LatticeFlags.retained J))
    (h : PolynomialFlagConvolution.CanonicalPair S T w) :
    forget I (source c w)=S ∧ forget J (target (k := k))=T := by
  constructor
  · apply PolynomialFlags.Flag.ext
    funext i
    apply PolynomialLattice.Lattice.ext
    change ((source c w).node ⟨i.val,retained_subset_full I i.property⟩).module = _
    rw [PolynomialCoordinateFlags.source_node_module]
    exact (h.2 i).symm
  · apply PolynomialFlags.Flag.ext
    funext i
    apply PolynomialLattice.Lattice.ext
    change ((target (k := k)).node ⟨i.val,retained_subset_full J i.property⟩).module = _
    rw [PolynomialCoordinateFlags.target_node_module]
    exact (h.1 i).symm

#print axioms relativePosition
#print axioms forget_pair
end Guralnick.PolynomialCanonicalFullFlags
