import Guralnick.MainFlagConvolution
import Guralnick.QuotientFlagData
import Guralnick.GalleryCounting

/-!
# The actual six-map gallery count

The convolution gallery is transported through proved equivalences to the
finite quotient gallery. Only general full-lattice theory and ordinary
finite-vector-space flag enumeration are input. The four-case polynomial
is a conclusion. Its intersection-rank parameters are explicit hypotheses
until the general orbit-matrix correspondence is applied separately.
-/

noncomputable section
namespace Guralnick.MainGalleryCount
open LaurentLattice LatticeGallery
open LatticeFlags LatticeFlags.Family

variable {k : Type} [Field k] {m : ℕ}
  {source : Flag k (2*m+1) (S m)} {target : Flag k (2*m+1) (O m)}

abbrev Space (target : Flag k (2*m+1) (O m)) :=
  QuotientSpace (base target) (upper target)

def quotientOrder (target : Flag k (2*m+1) (O m)) :=
  quotientIntervalIso (base target) (upper target) (stable k _ _)

def lower (h : Bounds source target) : Submodule k (Space target) :=
  (quotientOrder target).symm (I0 h)

def upperFlag (h : Bounds source target) : Submodule k (Space target) :=
  (quotientOrder target).symm (K0 h)

def flagF (hm : 2 ≤ m) (target : Flag k (2*m+1) (O m)) :
    Submodule k (Space target) :=
  (quotientOrder target).symm (endpointF hm)

def flagF' (hm : 2 ≤ m) (target : Flag k (2*m+1) (O m)) :
    Submodule k (Space target) :=
  (quotientOrder target).symm (endpointF' hm)

/-- Complete original-paper reduction of the main convolution galleries
 to the finite-vector-space galleries, before evaluating cardinalities. -/
def mainFiniteGalleryEquiv (hm : 2 ≤ m) (T : Theory k (2*m+1))
    (h : Bounds source target) :
    FlagConvolution.Gallery k (CanonicalChains.mainChain m) source target ≃
      GalleryFlags.Gallery (lower h) (upperFlag h) (flagF hm target) (flagF' hm target)
        m (2*m+1) :=
  (FlagConvolution.mainGalleryEquiv source target).trans (sixFiniteGalleryEquiv hm T h)

/-- The four-case Gaussian polynomial counts the genuine main-word
convolution galleries. The six-map count itself is not a literature input. -/
theorem main_gallery_count [Finite k]
    [FiniteDimensional k (Space target)] [Finite (Space target)]
    (hm : 2 ≤ m) (T : Theory k (2*m+1)) (h : Bounds source target)
    (hcount : GalleryCounting.FiniteFlagCounts k (Space target))
    {r l : ℕ} {a s β δ : ℤ} (hml : r+l=m)
    (hI : Module.finrank k (lower h) = r)
    (hK : Module.finrank k (upperFlag h) = 2*m+1-r)
    (ha : (Module.finrank k (lower h ⊓ flagF hm target : Submodule k (Space target)) : ℤ) = a)
    (hb : (Module.finrank k (lower h ⊓ flagF' hm target : Submodule k (Space target)) : ℤ) = a+β)
    (hc : (Module.finrank k (upperFlag h ⊓ flagF hm target : Submodule k (Space target)) : ℤ) = l+s)
    (hd : (Module.finrank k (upperFlag h ⊓ flagF' hm target : Submodule k (Space target)) : ℤ) = l+s+δ) :
    (Nat.card (FlagConvolution.Gallery k (CanonicalChains.mainChain m) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ) (CanonicalGallery.count l a s β δ) := by
  rw [Nat.card_congr (mainFiniteGalleryEquiv hm T h)]
  apply GalleryCounting.four_case_count hcount
    ((quotientOrder target).symm.monotone (I0_le_K0 h))
    ((quotientOrder target).symm.monotone (endpointF_le_endpointF' hm))
    hml (T.period_dimension (targetNode target)) hI hK
    (quotient_endpoint_dimensions hm T).2 ha hb hc hd

theorem lower_eq_bot (h : Bounds source target)
    (heq : sourceNode source = targetNode target) : lower h = ⊥ := by
  change quotientImage (base target) (upper target) _
    ((sourceNode source).space ⊔ (targetNode target).space)
    (I0 h).property.1 (I0 h).property.2 = ⊥
  rw [quotientImage_eq_map,heq,sup_idem]
  exact Submodule.mkQ_map_self _

theorem upperFlag_eq_top (h : Bounds source target)
    (heq : sourceNode source = targetNode target) : upperFlag h = ⊤ := by
  change quotientImage (base target) (upper target) _
    (expand (shift k (2*m+1)) (sourceNode source).space ⊓ upper target)
    (K0 h).property.1 (K0 h).property.2 = ⊤
  rw [quotientImage_eq_map,heq]
  change ((upper target ⊓ upper target).comap (upper target).subtype).map
    ((base target).comap (upper target).subtype).mkQ = ⊤
  simp [Submodule.map_top]

/-- At the fixed spherical lower endpoint the actual raw gallery count
is Y_m. Equality of its two degree-zero vertices is the exact source
condition; it is not replaced by arbitrary simple-module indices. -/
theorem main_source_gallery_count [Finite k]
    [FiniteDimensional k (Space target)] [Finite (Space target)]
    (hm : 2 ≤ m) (T : Theory k (2*m+1))
    (hcount : GalleryCounting.FiniteFlagCounts k (Space target))
    (heq : sourceNode source = targetNode target) :
    (Nat.card (FlagConvolution.Gallery k (CanonicalChains.mainChain m) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ) (Gaussian.Y m) := by
  have h : Bounds source target :=
    ⟨by simpa only [heq] using stable k (2*m+1) (targetNode target),
     by simpa only [heq] using stable k (2*m+1) (targetNode target)⟩
  rw [Nat.card_congr (mainFiniteGalleryEquiv hm T h),lower_eq_bot h heq,upperFlag_eq_top h heq]
  exact GalleryCounting.source_gallery_count hcount
    ((quotientOrder target).symm.monotone (endpointF_le_endpointF' hm))
    (T.period_dimension (targetNode target))
    (quotient_endpoint_dimensions hm T).1 (quotient_endpoint_dimensions hm T).2

end Guralnick.MainGalleryCount
