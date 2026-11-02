import Guralnick.PolynomialFlags
import Guralnick.FlagConvolution
import Guralnick.LatticeEquivariance
import Guralnick.PolynomialCoordinateFlags

/-!
# Polynomial affine-flag convolution at canonical endpoints

The convolution interface here is expressed solely in the
independent polynomial-lattice model. Canonical endpoints have the literal
coordinate modules and literal monomial window. Completion and arbitrary
completed changes of basis are handled by separate proved comparisons.
`PolynomialConvolutionConstruction.fromFullFlag` now constructs this
interface from binary full-flag convolution and proved elementary steps.
-/
noncomputable section
namespace Guralnick.PolynomialFlagConvolution
open Hecke ParabolicWeb CanonicalChains LatticeFlags PolynomialsFromCounts
variable {n : ℕ} {k : Type} [Field k]

/-- The standard endpoint pair in the polynomial Laurent model. -/
def CanonicalPair {I J : Index n}
    (source : PolynomialFlags.Flag k n (retained I))
    (target : PolynomialFlags.Flag k n (retained J)) (w : AffinePermutation n) : Prop :=
  (∀ i, (target.node i).module = PolynomialAffineCoordinates.coordinateModule k n i.val.val) ∧
  (∀ i, (source.node i).module = PolynomialAffineCoordinates.mapModule k n
    (PolynomialAffineCoordinates.windowEquiv k n w)
    (PolynomialAffineCoordinates.coordinateModule k n i.val.val))

/-- Canonical polynomial modules complete to the exact original coordinate endpoints. -/
theorem completed_nodes {I J : Index n}
    {source : PolynomialFlags.Flag k n (retained I)}
    {target : PolynomialFlags.Flag k n (retained J)} {w : AffinePermutation n}
    (h : CanonicalPair source target w) :
    (∀ i, ((PolynomialFlags.completeFlag target).node i).module =
      AffineLatticePosition.coordinateModule k n i.val.val) ∧
    (∀ i, ((PolynomialFlags.completeFlag source).node i).module =
      AffineLatticePosition.mapModule k n (AffineLatticePosition.windowEquiv k n w)
        (AffineLatticePosition.coordinateModule k n i.val.val)) := by
  constructor
  · intro i
    change LatticeCompletion.completeModule (target.node i).module = _
    rw [h.1 i,PolynomialAffineCoordinates.complete_coordinateModule]
  · intro i
    change LatticeCompletion.completeModule (source.node i).module = _
    rw [h.2 i,PolynomialAffineCoordinates.complete_window_coordinateModule]

theorem completed_position {I J : Index n}
    {source : PolynomialFlags.Flag k n (retained I)}
    {target : PolynomialFlags.Flag k n (retained J)} {w : AffinePermutation n}
    (h : CanonicalPair source target w) :
    AffineLatticePosition.RelativePosition k n (PolynomialFlags.completeFlag target)
      (PolynomialFlags.completeFlag source) w := by
  refine ⟨LinearEquiv.refl _ _,?_,?_⟩
  · intro i
    change Submodule.map (LinearMap.id : LaurentLattice.Ambient k n →ₗ[PowerSeries k] _)
      (AffineLatticePosition.coordinateModule k n i.val.val) = _
    rw [Submodule.map_id]
    exact ((completed_nodes h).1 i).symm
  · intro i
    exact ((completed_nodes h).2 i).symm

/-- The literal canonical polynomial pair exists for every pair of masks.
Its absolute degree and affine winding are proved, not literature fields. -/
theorem canonicalPair_realization [NeZero n] (c : WindowCoxeter n)
    (I J : Index n) (w : AffinePermutation n) :
    ∃ (source : PolynomialFlags.Flag k n (retained I))
      (target : PolynomialFlags.Flag k n (retained J)), CanonicalPair source target w := by
  refine ⟨PolynomialCoordinateFlags.source k n c w (retained I),
    PolynomialCoordinateFlags.target k n (retained J),?_,?_⟩
  · exact PolynomialCoordinateFlags.target_node_module k n (retained J)
  · exact PolynomialCoordinateFlags.source_node_module k n c w (retained I)

variable {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)

/-- General polynomial affine-flag convolution, with unchanged Hecke
normalization and arbitrary finite chains of finitary cyclic masks.
No completed-lattice comparison is included among these hypotheses. -/
structure Input : Prop where
  specialization : ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ {I J : Index n} (path : Chain I J)
      (source : PolynomialFlags.Flag (GaloisField p 2) n (retained I))
      (target : PolynomialFlags.Flag (GaloisField p 2) n (retained J)) (w : AffinePermutation n),
      CanonicalPair source target w →
      specialize p hp (K.standard.repr (Chain.raw K D L path) w) =
        ((primeUnit p hp) ^ (Chain.weight D path - c.system.length w)).val *
          (Nat.card (PolynomialFlags.Gallery path source target) : ℚ)

/-- Every completed endpoint pair is obtained from its canonical polynomial
pair by a single degree-preserving Laurent change of coordinates. All
intermediate flags and refinement choices are transported by that map. -/
theorem gallery_card_of_position {I J : Index n} (path : Chain I J)
    {psource : PolynomialFlags.Flag k n (retained I)}
    {ptarget : PolynomialFlags.Flag k n (retained J)} {w : AffinePermutation n}
    (hpoly : CanonicalPair psource ptarget w)
    (source : LatticeFlags.Flag k n (retained I))
    (target : LatticeFlags.Flag k n (retained J))
    (hpos : AffineLatticePosition.RelativePosition k n target source w) :
    Nat.card (FlagConvolution.Gallery k path source target) =
      Nat.card (PolynomialFlags.Gallery path psource ptarget) := by
  obtain ⟨g,ht,hs⟩ := hpos
  have hct := (completed_nodes hpoly).1
  have hcs := (completed_nodes hpoly).2
  have htarget (i : {i // i ∈ retained J}) :
      LatticeEquivariance.mapLattice g ((PolynomialFlags.completeFlag ptarget).node i) =
        target.node i := by
    apply LaurentLattice.Lattice.ext
    change AffineLatticePosition.mapModule k n g
      ((PolynomialFlags.completeFlag ptarget).node i).module = _
    rw [hct i]
    exact ht i
  have hsource (i : {i // i ∈ retained I}) :
      LatticeEquivariance.mapLattice g ((PolynomialFlags.completeFlag psource).node i) =
        source.node i := by
    apply LaurentLattice.Lattice.ext
    change AffineLatticePosition.mapModule k n g
      ((PolynomialFlags.completeFlag psource).node i).module = _
    rw [hcs i,← AffineLatticePosition.mapModule_trans]
    exact hs i
  obtain ⟨a,ha⟩ := FlagConvolution.retained_nonempty J
  have href : LaurentLattice.degree k n
      (LatticeEquivariance.mapLattice g ((PolynomialFlags.completeFlag ptarget).node ⟨a,ha⟩)) =
      LaurentLattice.degree k n ((PolynomialFlags.completeFlag ptarget).node ⟨a,ha⟩) := by
    rw [htarget]
    exact (target.degree_eq ⟨a,ha⟩).trans ((PolynomialFlags.completeFlag ptarget).degree_eq ⟨a,ha⟩).symm
  let hzero := LatticeEquivariance.degree_preserving_of_one g
    ((PolynomialFlags.completeFlag ptarget).node ⟨a,ha⟩) href
  have hft : LatticeEquivariance.flagEquiv g hzero (PolynomialFlags.completeFlag ptarget) = target := by
    apply LatticeFlags.Flag.ext
    funext i
    exact htarget i
  have hfs : LatticeEquivariance.flagEquiv g hzero (PolynomialFlags.completeFlag psource) = source := by
    apply LatticeFlags.Flag.ext
    funext i
    exact hsource i
  have he := Nat.card_congr (LatticeEquivariance.galleryEquiv g hzero path
    (PolynomialFlags.completeFlag psource) (PolynomialFlags.completeFlag ptarget))
  rw [hfs,hft] at he
  exact he.symm.trans (PolynomialFlags.gallery_card path psource ptarget).symm

/-- The completed convolution interface is derived from the polynomial one.
No completion, degree-component, cyclic-mask, or gallery comparison is a field. -/
def Input.toCompleted [NeZero n] (C : Input K D L) : FlagConvolution.Input K D L where
  realization := by
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    intro I J w
    obtain ⟨source,target,h⟩ := canonicalPair_realization (k := GaloisField p 2) c I J w
    exact ⟨PolynomialFlags.completeFlag source,PolynomialFlags.completeFlag target,completed_position h⟩
  specialization := by
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    intro I J path source target w hpos
    obtain ⟨psource,ptarget,hpoly⟩ := canonicalPair_realization (k := GaloisField p 2) c I J w
    have hc := gallery_card_of_position path hpoly source target hpos
    rw [hc]
    exact C.specialization p hp path psource ptarget w hpoly

#print axioms canonicalPair_realization
#print axioms gallery_card_of_position
#print axioms Input.toCompleted
end Guralnick.PolynomialFlagConvolution
