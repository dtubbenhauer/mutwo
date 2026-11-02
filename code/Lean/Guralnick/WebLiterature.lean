import Guralnick.MainFamilyCoordinate
import Guralnick.MainCanonicalSupport
import Guralnick.CanonicalSphericalTransition
import Guralnick.CanonicalRefinement
import Guralnick.AffineReflection

/-!
# The general literature used by the web proof

This bundle contains only framework results for arbitrary finite
parabolics, flags, finite vector spaces and affine windows. It contains no
family coordinate, six-position support, auxiliary canonicality, correction,
row sum, or first-cohomology conclusion. All those are separate obligations.
Each field remains a visible mathematical hypothesis, not a Lean axiom.
-/

noncomputable section
namespace Guralnick

structure WebLiterature {n : ℕ} [NeZero n] (T : Hecke.Theory n) where
  longest : ∀ I : ParabolicWeb.Index n, ParabolicWeb.LongestData T.coxeter I
  parabolic : ParabolicWeb.Laws T.kl longest
  schur : CanonicalSchur.Compatibility T.kl
  refinement : CanonicalRefinement.StandardCompatibility T.kl longest
  convolution : FlagConvolution.Input T.kl longest parabolic
  lattice_flags : GeneralLatticeFlagInput
  coordinates : MainPacketCoordinate.CoordinateInput n
  matrix_lengths : OrbitMatrix.ThreeColumnLengthInput T.coxeter
  block_lengths : FiniteBlocks.BlockLengthInput longest
  finite_longest : FiniteBlocks.StandardFiniteLongestInput longest
  diagram_invariance : AffineReflection.DiagramInvarianceInput T.kl

namespace WebLiterature
open Hecke ParabolicWeb Positivity CanonicalRowSum
open scoped BigOperators

variable {m : ℕ} (hm : 2≤m) (T : Theory (2*m+1)) (W : WebLiterature T)

abbrev raw : Hecke.Algebra (2*m+1) := Family.raw T.kl W.longest W.parabolic

include hm W

/-- The original marked-family standard coefficient is derived, not imported. -/
theorem marked_coordinate (j : Fin m) :
    T.kl.standard.repr W.raw (familyIndex hm j) =
      normalize (CanonicalGallery.gap ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1)
        (CanonicalGallery.count ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1) :=
  MainFamilyCoordinate.marked_raw_coordinate T.kl W.longest W.parabolic
    hm (by omega) (by omega) W.convolution W.lattice_flags W.coordinates W.matrix_lengths
    W.block_lengths W.finite_longest

/-- The original full-spherical raw coordinate is derived for all ranks. -/
theorem full_coordinate (r : ℕ) (hr : r≤m) :
    T.kl.standard.repr W.raw (CanonicalSpherical.index m r) =
      CanonicalFullCorrection.rawCoordinate (m-r) :=
  MainFamilyCoordinate.spherical_raw_coordinate T.kl W.longest W.parabolic hm hr
    W.convolution W.lattice_flags W.coordinates W.matrix_lengths
    W.block_lengths W.finite_longest

/-- The complete spherical canonical transition is derived from actual
auxiliary galleries and the canonical basis argument. -/
theorem full_transition (s r : ℕ) (hs : s≤m) (hr : r≤m) :
    T.kl.standard.repr (T.kl.canonical (CanonicalSpherical.index m s))
      (CanonicalSpherical.index m r) =
      if r≤s then CanonicalFullCorrection.transition (m-r) (s-r) else 0 :=
  CanonicalSphericalTransition.transition_matrix hm T.kl W.longest W.parabolic
    W.convolution W.lattice_flags W.coordinates W.block_lengths W.finite_longest
    T.positivity W.schur W.matrix_lengths s r hs hr

/-- At this assembly stage exactly the three original contribution bounds
remain explicit. They are not fields of WebLiterature and are not claimed
as published inputs. All raw counts and spherical transitions are proved. -/
theorem row_sum_of_contribution_bounds
    (hauxFamily : ∀ (j : Fin m) w, (∀ k : Fin m, w≠familyIndex hm k) →
      LowerBound (T.kl.canonical.repr W.raw w *
        T.kl.standard.repr (T.kl.canonical w) (familyIndex hm j)) 1)
    (hnonsphericalAtZ : ∀ r<m-1, ∀ w, (∀ s<m-1, w≠CanonicalSpherical.index m s) →
      LowerBound (T.kl.canonical.repr W.raw w *
        T.kl.standard.repr (T.kl.canonical w) (CanonicalSpherical.index m r)) 1)
    (hauxSource : ∀ w, (∀ j : Fin m, w≠familyIndex hm j) →
      (∀ r<m-1, w≠CanonicalSpherical.index m r) →
      LowerBound (T.kl.canonical.repr W.raw w *
        T.kl.standard.repr (T.kl.canonical w) (AffinePermutation.longest (2*m+1))) 3) :
    (∑ j : Fin m, familyMu hm (show 1≤j.val+1 by omega) (by omega) T.kl) =
      (Nat.choose (m+1) 2 : ℤ) := by
  apply CanonicalSpherical.row_sum_of_local_coordinate_identities hm T.kl W.longest
    W.parabolic T.positivity (marked_coordinate hm T W) hauxFamily
  · intro r hr
    exact full_coordinate hm T W r (by omega)
  · intro r hr s hs
    exact full_transition hm T W s r (by omega) (by omega)
  · exact hnonsphericalAtZ
  · exact hauxSource

end WebLiterature
end Guralnick
