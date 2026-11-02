import Guralnick.CanonicalSphericalSupport
import Guralnick.CanonicalAuxiliarySource
import Guralnick.OrbitQuotientRanks
import Guralnick.MainOrbitRanks
import Guralnick.FiniteAuxiliaryBlocks

/-! # Spherical gallery support and coordinates from actual lattice orbits -/
noncomputable section
namespace Guralnick.CanonicalSphericalCoordinates
open LaurentLattice LatticeGallery LatticeFlags CanonicalChains CanonicalFlagAuxiliary
  OrbitMatrix WindowPacketMatrix AffineLatticePosition

variable {k : Type} [Field k] {m : ℕ}

abbrev Boundary (k : Type) [Field k] (m : ℕ) :=
  Flag k (2*m+1) (retained (CanonicalChains.source (show 0<2*m+1 by omega)))

abbrev base (F : Boundary k m) : Lattice k (2*m+1) :=
  targetLattice (show 0<2*m+1 by omega) F

structure Coordinates (source target : Boundary k m) (w : AffinePermutation (2*m+1)) where
  basis : Ambient k (2*m+1) ≃ₗ[LaurentSeries k] Ambient k (2*m+1)
  target_zero : targetCut k (2*m+1) basis 0 = (base target).space
  source_zero : sourceCut k (2*m+1) basis w 0 = (base source).space

noncomputable def coordinates {source target : Boundary k m} {w : AffinePermutation (2*m+1)}
    (hpos : RelativePosition k (2*m+1) target source w) : Coordinates source target w := by
  let g := Classical.choose (relativePosition_cuts k (2*m+1) hpos)
  have hg := Classical.choose_spec (relativePosition_cuts k (2*m+1) hpos)
  exact ⟨g,hg.1 ⟨⟨0,by omega⟩,(retained_omit _ _).mpr rfl⟩,
    hg.2 ⟨⟨0,by omega⟩,(retained_omit _ _).mpr rfl⟩⟩

variable {source target : Boundary k m} {w : AffinePermutation (2*m+1)}
  (C : Coordinates source target w) (input : CoordinateDimensionInput k (2*m+1))

 theorem Coordinates.target_top : targetCut k (2*m+1) C.basis (2*m+1 : ℕ) =
    expand (shift k (2*m+1)) (base target).space := by
  rw [targetCut_period,C.target_zero]

theorem Coordinates.source_top : sourceCut k (2*m+1) C.basis w (2*m+1 : ℕ) =
    expand (shift k (2*m+1)) (base source).space := by
  rw [sourceCut_period,C.source_zero]

include C input

theorem supported_of_bounds (h : EndpointBounds (base source) (base target)) : Supported w := by
  have hw : ∀ z : ℤ, z≤0 → w.onIntegers z≤(2*m+1 : ℕ) := by
    apply (input.source_le_target C.basis w (2*m+1 : ℕ) 0).mp
    rw [C.source_zero,C.target_top]
    exact h.source_le
  have hwi : ∀ z : ℤ, z≤0 → (w⁻¹).onIntegers z≤(2*m+1 : ℕ) := by
    rw [onIntegers_inv]
    apply (input.target_le_source C.basis w 0 (2*m+1 : ℕ)).mp
    rw [C.target_zero,C.source_top]
    exact h.target_le
  intro i
  constructor
  · have hh := winding_upper_of_cut_bound w hw (w.residue.symm i)
    change -1≤ -w.winding (w.residue.symm i)
    omega
  · exact winding_upper_of_cut_bound (w⁻¹) hwi i

def bounds_of_supported (hs : Supported w) : EndpointBounds (base source) (base target) := by
  have hw : ∀ i, w.winding i≤1 := by
    intro i
    have h := (hs (w.residue i)).1
    change -1≤ -w.winding (w.residue.symm (w.residue i)) at h
    rw [Equiv.symm_apply_apply] at h
    omega
  constructor
  · rw [← C.source_zero,← C.target_top]
    apply (input.source_le_target C.basis w (2*m+1 : ℕ) 0).mpr
    exact cut_bound_of_winding_upper w hw
  · rw [← C.target_zero,← C.source_top]
    apply (input.target_le_source C.basis w 0 (2*m+1 : ℕ)).mpr
    rw [← onIntegers_inv]
    exact cut_bound_of_winding_upper (w⁻¹) (fun i => (hs i).2)

theorem lower_rank (h : EndpointBounds (base source) (base target)) (hs : Supported w) :
    Module.finrank k (finiteLower (base source) (base target) h) =
      (packetMatrix m w hs).rank := by
  rw [← cumulative_rank m w hs]
  exact quotient_lower_rank input C.basis w _ _ (stable k _ (base target))
    (lowerEndpoint _ _ h) (2*m+1) 0 C.target_zero C.target_top
    (by change _ = _; rw [C.source_zero]; rfl)

theorem upper_rank (h : EndpointBounds (base source) (base target)) (hs : Supported w) :
    Module.finrank k (finiteUpper (base source) (base target) h) =
      2*m+1-(packetMatrix m w hs).rank := by
  rw [← cumulative_corank m w hs]
  exact quotient_upper_rank input C.basis w _ _ (stable k _ (base target))
    (upperEndpoint _ _ h) (2*m+1) (2*m+1 : ℕ) C.target_zero C.target_top
    (by change _ = _; rw [C.source_top]; rfl)
    (by rw [C.source_top]; exact h.target_le)

/-- Nonempty spherical galleries impose both the support bound and r≤s. -/
theorem gallery_supported_rank (T : Theory k (2*m+1)) (s : Fin (2*m+1)) (hs : 0<s.val)
    (g : FlagConvolution.Gallery k (sphericalChain (by omega) s) source target) :
    ∃ h : Supported w, (packetMatrix m w h).rank≤s.val := by
  let d := sphericalGalleryEquiv (by omega) s hs source target g
  let h : EndpointBounds (base source) (base target) := d.endpointBounds
  let hw := supported_of_bounds C input h
  letI := T.period_finite (base target)
  let fg : GalleryCounting.IntermediateSubspace (finiteLower (base source) (base target) h)
      (finiteUpper (base source) (base target) h) s.val :=
    sphericalFiniteGalleryEquiv T (show 0<2*m+1 by omega) s hs source target h g
  have hdim := Submodule.finrank_mono fg.property.1
  rw [lower_rank C input h hw,fg.property.2.2] at hdim
  exact ⟨hw,hdim⟩

/-- The Gaussian spherical count at every actual endpoint of bounded support. -/
theorem gallery_count [Finite k] (T : Theory k (2*m+1))
    [FiniteDimensional k (quotientSpace (base target))]
    [Finite (quotientSpace (base target))]
    (hcount : GalleryCounting.FiniteFlagCounts k (quotientSpace (base target)))
    (s : Fin (2*m+1)) (hs : 0<s.val) (hw : Supported w) :
    (Nat.card (FlagConvolution.Gallery k (sphericalChain (by omega) s) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ)
        (CanonicalGallery.qGauss ((2*m+1 : ℕ) - 2*((packetMatrix m w hw).rank : ℤ))
          ((s.val : ℤ)-(packetMatrix m w hw).rank)) := by
  let h := bounds_of_supported C input hw
  exact spherical_gallery_count T (show 0<2*m+1 by omega) s hs source target h hcount _
    (lower_rank C input h hw) (upper_rank C input h hw)

end Guralnick.CanonicalSphericalCoordinates
