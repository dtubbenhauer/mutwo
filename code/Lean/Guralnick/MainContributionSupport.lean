import Guralnick.WebLiterature
import Guralnick.PacketIndexClassification
import Guralnick.PacketReflection

/-!
# Actual indices and multiplicity bounds for the final readout

The six numerical patterns here are extracted from the nonzero canonical
support of the actual six-map element. Type F is identified with the
prescribed affine family; the full pattern is identified with Zᵣ.
-/
noncomputable section
namespace Guralnick.WebLiterature
open Hecke ParabolicWeb Positivity CanonicalRowSum CanonicalMultiplicityBounds
open WindowPacketMatrix CanonicalMatrix CanonicalCorrection

variable {m : ℕ} (hm : 2≤m) (T : Theory (2*m+1)) (W : WebLiterature T)
include hm W

theorem term_maximal (w : AffinePermutation (2*m+1))
    (hne : T.kl.canonical.repr W.raw w ≠ 0) :
    CanonicalSchur.DoubleMaximal T.coxeter (Family.output m) (Family.source m) w :=
  CanonicalSchur.raw_doubleMaximal T.kl W.longest W.parabolic W.schur w hne

theorem term_pattern (w : AffinePermutation (2*m+1))
    (hne : T.kl.canonical.repr W.raw w ≠ 0) :
    ∃ hs : Supported w, ∃ p : Pattern, Matches (packetMatrix m w hs) p := by
  obtain ⟨hs,h⟩ := MainCanonicalSupport.raw_six_position_support T.kl W.longest
    W.parabolic T.positivity hm W.convolution W.lattice_flags W.coordinates
    W.matrix_lengths W.block_lengths W.finite_longest W.schur w hne
  obtain ⟨p,hp⟩ := pattern_of_six _ h
  exact ⟨hs,p,hp⟩

theorem packet_coordinate (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0) :
    let A:=packetMatrix m w hs
    T.kl.standard.repr W.raw w =
      normalize (CanonicalGallery.gap A.corank A.a A.s A.beta A.delta)
        (CanonicalGallery.count A.corank A.a A.s A.beta A.delta) := by
  have h:=MainPacketCoordinate.raw_packet_coordinate T.kl W.longest W.parabolic hm
    W.convolution W.lattice_flags W.coordinates W.matrix_lengths W.block_lengths
    W.finite_longest w hs (term_maximal hm T W w hne)
  dsimp only at h ⊢
  rwa [(packetMatrix m w hs).raw_gap] at h

theorem pattern_coordinate (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0) (p : Pattern)
    (hp : Matches (packetMatrix m w hs) p) :
    T.kl.standard.repr W.raw w =
      normalize (CanonicalGallery.gap (packetMatrix m w hs).corank
        (a p) (s p) (beta p) (delta p))
        (CanonicalGallery.count (packetMatrix m w hs).corank (a p) (s p) (beta p) (delta p)) := by
  simpa only [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2] using packet_coordinate hm T W w hs hne

theorem two_is_family (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0)
    (hp : Matches (packetMatrix m w hs) .two) :
    ∃ j : Fin m, w=familyIndex hm j := by
  have h:=PacketIndexClassification.typeF_index hm T.coxeter W.matrix_lengths w hs
    (term_maximal hm T W w hne) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  let A:=packetMatrix m w hs
  have hr:=A.typeF_rank_positive hp.1
  refine ⟨⟨A.rank-1,by have hh:=A.rank_le; omega⟩,?_⟩
  have he : A.rank-1+1=A.rank := by omega
  simpa only [familyIndex,he] using h

theorem corank_positive_off_family (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0)
    (hoff : ∀ j : Fin m, w≠familyIndex hm j) :
    1≤(packetMatrix m w hs).corank := by
  let A:=packetMatrix m w hs
  change 1≤A.corank
  have hn:=A.corank_nonnegative
  by_contra hn'
  have hz : A.corank=0 := by omega
  have hc:=packet_coordinate hm T W w hs hne
  change T.kl.standard.repr W.raw w = normalize (CanonicalGallery.gap A.corank
    A.a A.s A.beta A.delta) (CanonicalGallery.count A.corank A.a A.s A.beta A.delta) at hc
  rw [hz] at hc
  obtain ⟨hb,hd,ha,hs'⟩ := CanonicalApplication.raw_boundary_position T.kl W.longest
    W.parabolic T.positivity w A.a A.s A.beta A.delta A.a_nonnegative A.middle_cases
    (A.boundary_first hz) (A.boundary_last hz) hc hne
  obtain ⟨j,hj⟩:=two_is_family hm T W w hs hne ⟨ha,hs',hb,hd⟩
  exact hoff j hj

theorem term_multiplicity_lowerBound (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0) (p : Pattern)
    (hp : Matches (packetMatrix m w hs) p) (hl : 1≤(packetMatrix m w hs).corank) :
    LowerBound (T.kl.canonical.repr W.raw w) (-allowance p (packetMatrix m w hs).corank) :=
  (pattern_multiplicity_bounds T.kl W.longest W.parabolic T.positivity w p _ hl
    (pattern_coordinate hm T W w hs hne p hp)).1

theorem term_allowance_nonnegative (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0) (p : Pattern)
    (hp : Matches (packetMatrix m w hs) p) (hl : 1≤(packetMatrix m w hs).corank) :
    0≤allowance p (packetMatrix m w hs).corank := by
  by_contra h
  exact hne (pattern_vanishes T.kl W.longest W.parabolic T.positivity w p _ hl
    (by omega) (pattern_coordinate hm T W w hs hne p hp))

theorem full_is_spherical (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0)
    (hp : Matches (packetMatrix m w hs) .full) :
    w=CanonicalSpherical.index m (packetMatrix m w hs).rank :=
  PacketIndexClassification.full_pattern_index hm T.coxeter W.matrix_lengths w hs
    (term_maximal hm T W w hne) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

theorem full_rank_lt (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0)
    (hp : Matches (packetMatrix m w hs) .full)
    (hoff : ∀ j : Fin m, w≠familyIndex hm j) :
    (packetMatrix m w hs).rank < m-1 := by
  have hl:=corank_positive_off_family hm T W w hs hne hoff
  have ha:=term_allowance_nonnegative hm T W w hs hne .full hp hl
  simp only [allowance,PacketMatrix.corank] at ha
  omega

/-- The full-spherical terms are at least six degrees above the critical
constant readout at a marked family standard. Smaller ranks give zero. -/
theorem full_family_contribution (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hne : T.kl.canonical.repr W.raw w ≠ 0)
    (hp : Matches (packetMatrix m w hs) .full)
    (hoff : ∀ j : Fin m, w≠familyIndex hm j) (j : Fin m) :
    LowerBound (T.kl.canonical.repr W.raw w *
      T.kl.standard.repr (T.kl.canonical w) (familyIndex hm j)) 1 := by
  let A:=packetMatrix m w hs
  have hl:=corank_positive_off_family hm T W w hs hne hoff
  have hmultip:=term_multiplicity_lowerBound hm T W w hs hne .full hp hl
  have hw:=full_is_spherical hm T W w hs hne hp
  change w=CanonicalSpherical.index m A.rank at hw
  by_cases hr : j.val+1≤A.rank
  · have hc:=CanonicalRefinement.spherical_refined_lowerBound T.kl W.longest W.refinement
      hm (show 1≤j.val+1 by omega) (show j.val+1≤m by omega) A.rank_le
    rw [←hw] at hc
    apply lowerBound_mono (lowerBound_mul hmultip hc)
    simp only [allowance,PacketMatrix.corank]
    dsimp only [A] at hr
    omega
  · have hc:=CanonicalRefinement.spherical_at_family T.kl W.longest W.refinement
      (j:=j.val+1) (s:=A.rank) hm (by omega) (by omega) A.rank_le
    rw [full_transition hm T W A.rank (j.val+1) A.rank_le (by omega),if_neg hr,mul_zero] at hc
    change T.kl.standard.repr (T.kl.canonical (CanonicalSpherical.index m A.rank))
      (familyIndex hm j)=0 at hc
    rw [hw,hc,mul_zero]
    intro e he
    rfl

/-- A surviving marked-family multiplicity is exactly one, even before
the descending readout has proved that every family member survives. -/
theorem family_term_one (j : Fin m)
    (hne : T.kl.canonical.repr W.raw (familyIndex hm j) ≠ 0) :
    T.kl.canonical.repr W.raw (familyIndex hm j)=1 := by
  exact (CanonicalApplication.raw_typeF_zero_or_one T.kl W.longest W.parabolic
    T.positivity (familyIndex hm j) (m-(j.val+1)) (marked_coordinate hm T W j)).resolve_left hne

end Guralnick.WebLiterature
