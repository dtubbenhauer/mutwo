import Guralnick.OrbitQuotientRanks
import Guralnick.MainOrbitRanks
import Guralnick.CanonicalOneLineFlags
import Guralnick.WindowPacketMatrix

/-! # Actual orbit coordinates for the one-retained-line web

All endpoint ranks are dimensions of genuine quotient subspaces. Their
values follow from the generic periodic-coordinate theorem and literal
finite window counts; the two-case gallery polynomial is then a conclusion.
-/
noncomputable section
namespace Guralnick.OneLineOrbit
open LaurentLattice LatticeGallery LatticeFlags AffineLatticePosition OrbitMatrix
open CanonicalChains CanonicalFlagAuxiliary CanonicalOneLineFlags WindowPacketMatrix

variable {k : Type} [Field k] {N : ℕ} [NeZero N]
  (hn : 1<N) (f : Fin N)
  (source : Flag k N (retained (src hn)))
  (target : Flag k N (retained (out hn f)))

abbrev A := singleNode (⟨0,Nat.zero_lt_of_lt hn⟩ : Fin N) source
abbrev B := targetBase hn f target
abbrev F := targetF hn f target

structure Coordinates (w : AffinePermutation N) where
  basis : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N
  zero : targetCut k N basis 0 = (B hn f target).space
  line : targetCut k N basis f.val = (F hn f target).space
  source : sourceCut k N basis w 0 = (A hn source).space

def coordinates {w : AffinePermutation N} (h : RelativePosition k N target source w) :
    Coordinates hn f source target w := by
  let g := Classical.choose (relativePosition_cuts k N h)
  have ht := (Classical.choose_spec (relativePosition_cuts k N h)).1
  have hs := (Classical.choose_spec (relativePosition_cuts k N h)).2
  exact ⟨g,ht ⟨⟨0,Nat.zero_lt_of_lt hn⟩,(out_mask hn f _).mpr (Or.inl rfl)⟩,
    ht ⟨f,(out_mask hn f _).mpr (Or.inr rfl)⟩,
    hs ⟨⟨0,Nat.zero_lt_of_lt hn⟩,(retained_omit _ _).mpr rfl⟩⟩

variable {hn f source target} {w : AffinePermutation N}
  (C : Coordinates hn f source target w)
  (input : CoordinateDimensionInput k N)

theorem Coordinates.top : targetCut k N C.basis N = expand (shift k N) (B hn f target).space := by
  rw [targetCut_period,C.zero]

theorem Coordinates.sourceTop : sourceCut k N C.basis w N = expand (shift k N) (A hn source).space := by
  rw [sourceCut_period,C.source]

include C input

def Coordinates.bounds (hs : Supported w) : EndpointBounds (A hn source) (B hn f target) := by
  have hw : ∀ i, w.winding i ≤ 1 := by
    intro i
    have ht := (hs (w.residue i)).1
    change -1 ≤ -w.winding (w.residue.symm (w.residue i)) at ht
    rw [Equiv.symm_apply_apply] at ht
    omega
  constructor
  · rw [← C.source,← C.top]
    exact (input.source_le_target C.basis w N 0).mpr (cut_bound_of_winding_upper w hw)
  · rw [← C.zero,← C.sourceTop]
    apply (input.target_le_source C.basis w 0 N).mpr
    rw [← onIntegers_inv]
    exact cut_bound_of_winding_upper (w⁻¹) (fun i => (hs i).2)

theorem Coordinates.supported (h : EndpointBounds (A hn source) (B hn f target)) : Supported w := by
  have hw : ∀ z : ℤ, z≤0 → w.onIntegers z≤N := by
    apply (input.source_le_target C.basis w N 0).mp
    rw [C.source,C.top]
    exact h.source_le
  have hi : ∀ z : ℤ, z≤0 → (w⁻¹).onIntegers z≤N := by
    rw [onIntegers_inv]
    apply (input.target_le_source C.basis w 0 N).mp
    rw [C.zero,C.sourceTop]
    exact h.target_le
  intro i
  constructor
  · have hneg := winding_upper_of_cut_bound w hw (w.residue.symm i)
    change -1 ≤ -w.winding (w.residue.symm i)
    omega
  · exact winding_upper_of_cut_bound (w⁻¹) hi i

variable (h : EndpointBounds (A hn source) (B hn f target))

theorem lower_rank :
    Module.finrank k (finiteLower (A hn source) (B hn f target) h) =
      cumulativeCount N w 0 N 0 := by
  apply quotient_lower_rank input C.basis w _ _ _
    (lowerEndpoint (A hn source) (B hn f target) h) N 0 C.zero C.top
  change (A hn source).space ⊔ (B hn f target).space = _
  rw [C.source]

theorem upper_rank :
    Module.finrank k (finiteUpper (A hn source) (B hn f target) h) =
      cumulativeCount N w 0 N N := by
  apply quotient_upper_rank input C.basis w _ _ _
    (upperEndpoint (A hn source) (B hn f target) h) N N C.zero C.top
  · change expand (shift k N) (A hn source).space ⊓ expand (shift k N) (B hn f target).space = _
    rw [C.sourceTop]
  · rw [C.sourceTop]
    exact h.target_le

theorem lower_intersection :
    Module.finrank k (finiteLower (A hn source) (B hn f target) h ⊓
      finiteF (B hn f target) (F hn f target) (targetBase_le_F hn f target)
        (targetF_le_period hn f target) : Submodule k (quotientSpace (B hn f target))) =
      cumulativeCount N w 0 f.val 0 := by
  apply quotient_lower_intersection input C.basis w _ _ _
    (lowerEndpoint (A hn source) (B hn f target) h)
    ⟨(F hn f target).space,targetBase_le_F hn f target,targetF_le_period hn f target⟩
    f.val 0 C.zero C.line
  change (A hn source).space ⊔ (B hn f target).space = _
  rw [C.source]

theorem upper_intersection :
    Module.finrank k (finiteUpper (A hn source) (B hn f target) h ⊓
      finiteF (B hn f target) (F hn f target) (targetBase_le_F hn f target)
        (targetF_le_period hn f target) : Submodule k (quotientSpace (B hn f target))) =
      cumulativeCount N w 0 f.val N := by
  apply quotient_upper_intersection input C.basis w _ _ _
    (upperEndpoint (A hn source) (B hn f target) h)
    ⟨(F hn f target).space,targetBase_le_F hn f target,targetF_le_period hn f target⟩
    f.val N C.zero C.line
  · change expand (shift k N) (A hn source).space ⊓ expand (shift k N) (B hn f target).space = _
    rw [C.sourceTop]
  · rw [C.sourceTop]
    exact h.target_le

/-- A nonempty actual one-line gallery forces supported inverse windings. -/
theorem supported_of_nonempty (j : Fin N) (hj : 1≤j.val) (hf : 1≤f.val)
    (T : Theory k N)
    (hg : Nonempty (FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target)) :
    Supported w := by
  obtain ⟨g⟩ := hg
  let d := oneLineGalleryEquiv hn j f hj hf source target T g
  exact C.supported input d.spherical.endpointBounds

include h

/-- The rank bound used by the canonical degree test follows from the
actual intermediate j-plane in a nonempty gallery. -/
theorem rank_le_of_nonempty (j : Fin N) (hj : 1≤j.val) (hf : 1≤f.val)
    (T : Theory k N)
    (hg : Nonempty (FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target)) :
    cumulativeCount N w 0 N 0 ≤ j.val := by
  obtain ⟨g⟩ := hg
  let d := oneLineFiniteGalleryEquiv hn j f hj hf source target T h g
  letI := T.period_finite (B hn f target)
  have hd := Submodule.finrank_mono d.I₀_le_U
  rw [d.U_dim,lower_rank C input h] at hd
  exact hd

/-- Intermediate form of the original two-case count. Its four numerical
hypotheses concern literal finite counts of the actual window and are
subsequently discharged by the packet-matrix calculation. Signed Gaussian
indices retain all invalid-rank zero cases. -/
theorem one_line_count_of_cumulative [Finite k]
    [FiniteDimensional k (quotientSpace (B hn f target))]
    [Finite (quotientSpace (B hn f target))]
    (j : Fin N) (hj : 1≤j.val) (hf : 1≤f.val) (T : Theory k N)
    (hcount : GalleryCounting.FiniteFlagCounts k (quotientSpace (B hn f target)))
    (r : ℕ) (hr : r≤N) (a b : ℤ)
    (hI : cumulativeCount N w 0 N 0 = r)
    (hK : cumulativeCount N w 0 N N = N-r)
    (ha : (cumulativeCount N w 0 f.val 0 : ℤ) = a)
    (hc : (cumulativeCount N w 0 f.val N : ℤ) = (f.val : ℤ)-r+b) :
    (Nat.card (FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ)
        (CanonicalAuxiliary.oneLineCount ((N : ℤ)-2*r) ((j.val : ℤ)-r)
          ((f.val : ℤ)-r) a b) := by
  apply one_line_gallery_count hn j f hj hf source target T h hcount
  · rw [upper_rank C input h,lower_rank C input h,hI,hK,Int.ofNat_sub hr]
    ring
  · rw [lower_rank C input h,hI]
  · rw [lower_intersection C input h]
    exact ha
  · rw [upper_intersection C input h]
    exact hc

end Guralnick.OneLineOrbit
