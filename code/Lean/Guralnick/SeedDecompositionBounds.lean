import Guralnick.MainContributionBounds
import Guralnick.PolynomialWebLiterature

/-! # Constant multiplicities in the first six-map web

At `m = 2`, the relevance bounds leave only the two marked terms, the
two strong one-line terms, and the origin.  Away from the origin every
canonical multiplicity is constant.  The diagonal constant-term argument
then reads that multiplicity from the actual gallery polynomial.
-/

noncomputable section
set_option maxHeartbeats 1200000
namespace Guralnick.SeedDecomposition
open Hecke ParabolicWeb Positivity CanonicalRowSum CanonicalMultiplicityBounds
open CanonicalCorrection WindowPacketMatrix CanonicalMatrix

variable (T : Hecke.Theory 5) (W : WebLiterature T)

private theorem zero_bound (b : ℤ) : LowerBound (0 : LP) b := by
  intro e he
  rfl

/-- Every canonical multiplicity except the full spherical origin has
nonnegative Laurent support in the first example. -/
theorem outside_origin_lowerBound (w : AffinePermutation 5)
    (hw : w ≠ AffinePermutation.longest 5) :
    LowerBound (T.kl.canonical.repr (W.raw (m := 2)) w) 0 := by
  by_cases hz : T.kl.canonical.repr (W.raw (m := 2)) w = 0
  · rw [hz]
    exact zero_bound 0
  by_cases hf : ∃ j : Fin 2, w = familyIndex (by decide : 2 ≤ 2) j
  · obtain ⟨j, rfl⟩ := hf
    rw [W.family_term_one (by decide) T j hz]
    intro e he
    change Finsupp.single 0 (1 : ℤ) e = 0
    simp only [Finsupp.single_apply, if_neg (show (0 : ℤ) ≠ e by omega)]
  have hoff : ∀ j : Fin 2, w ≠ familyIndex (by decide : 2 ≤ 2) j := by
    simpa only [not_exists] using hf
  obtain ⟨hs, p, hp⟩ := W.term_pattern (by decide : 2 ≤ 2) T w hz
  by_cases hpf : p = .full
  · subst p
    have hr := W.full_rank_lt (by decide : 2 ≤ 2) T w hs hz hp hoff
    have hi := W.full_is_spherical (by decide : 2 ≤ 2) T w hs hz hp
    have hr0 : (packetMatrix 2 w hs).rank = 0 := by omega
    rw [hr0, CanonicalSpherical.index_zero] at hi
    exact False.elim (hw hi)
  have hpt : p ≠ .two := by
    intro he
    subst p
    obtain ⟨j, hj⟩ := W.two_is_family (by decide : 2 ≤ 2) T w hs hz hp
    exact hoff j hj
  obtain ⟨r, hr, hrm, hd⟩ := W.auxiliary_data (by decide : 2 ≤ 2) T
    w hs hz p hp hpf hpt hoff
  have hr1 : r.val = 1 := by omega
  rcases hd with ⟨hb, _⟩ | ⟨hb, _⟩
  · simpa only [hr1] using hb
  · exact lowerBound_mono hb (by rw [hr1]; norm_num)

/-- The surviving auxiliary indices are precisely the two strong words;
the weak alternatives have positive bar-invariant multiplicity and vanish. -/
theorem auxiliary_word (w : AffinePermutation 5)
    (hne : T.kl.canonical.repr (W.raw (m := 2)) w ≠ 0)
    (hw : w ≠ AffinePermutation.longest 5)
    (hoff : ∀ j : Fin 2, w ≠ familyIndex (by decide : 2 ≤ 2) j) :
    CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
      (1 : Fin 5) (2 : Fin 5) = T.kl.canonical w ∨
    CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
      (1 : Fin 5) (2 : Fin 5) = T.kl.canonical (AffineReflection.reflect w) := by
  obtain ⟨hs, p, hp⟩ := W.term_pattern (by decide : 2 ≤ 2) T w hne
  have hpf : p ≠ .full := by
    intro he
    subst p
    have hr := W.full_rank_lt (by decide : 2 ≤ 2) T w hs hne hp hoff
    have hi := W.full_is_spherical (by decide : 2 ≤ 2) T w hs hne hp
    have hr0 : (packetMatrix 2 w hs).rank = 0 := by omega
    rw [hr0, CanonicalSpherical.index_zero] at hi
    exact hw hi
  have hpt : p ≠ .two := by
    intro he
    subst p
    obtain ⟨j, hj⟩ := W.two_is_family (by decide : 2 ≤ 2) T w hs hne hp
    exact hoff j hj
  obtain ⟨r, hr, hrm, hd⟩ := W.auxiliary_data (by decide : 2 ≤ 2) T
    w hs hne p hp hpf hpt hoff
  have hr1 : r = (1 : Fin 5) := by
    apply Fin.ext
    change r.val = 1
    omega
  rcases hd with ⟨_, hword⟩ | ⟨hb, _⟩
  · simpa only [hr1] using hword
  · exact False.elim (hne (eq_zero_of_positive_bar_bound
      (Family.raw_canonical_bar (m := 2) T.kl W.longest W.parabolic w) hb
      (by rw [hr1]; norm_num)))

/-- A non-origin standard with constant coefficient one has canonical
multiplicity one, provided the origin canonical element does not reach it.
All other contributions vanish in degree zero by ordinary KL triangularity. -/
theorem multiplicity_one_of_constant (w : AffinePermutation 5)
    (hw : w ≠ AffinePermutation.longest 5)
    (hsource : T.kl.standard.repr (T.kl.canonical (AffinePermutation.longest 5)) w = 0)
    (hconstant : T.kl.standard.repr (W.raw (m := 2)) w 0 = 1) :
    T.kl.canonical.repr (W.raw (m := 2)) w = 1 := by
  classical
  let S := insert w (T.kl.canonical.repr (W.raw (m := 2))).support
  apply CanonicalBasis.multiplicity_one S
    (fun z => T.kl.canonical.repr (W.raw (m := 2)) z)
    (fun y z => T.kl.standard.repr (T.kl.canonical z) y)
    (fun y => T.kl.standard.repr (W.raw (m := 2)) y) w
    (Finset.mem_insert_self _ _) (T.kl.canonical_diagonal w)
    (CanonicalBasis.coordinate_expansion_on T.kl.standard T.kl.canonical
      (W.raw (m := 2)) S (Finset.subset_insert _ _) w)
    (Family.raw_canonical_bar (m := 2) T.kl W.longest W.parabolic w)
    (outside_origin_lowerBound T W w hw) hconstant
  intro z hz hzw
  by_cases hz0 : z = AffinePermutation.longest 5
  · rw [hz0, hsource, mul_zero]
    exact zero_bound 1
  · simpa only [zero_add] using lowerBound_mul
      (outside_origin_lowerBound T W z hz0) (T.kl.canonical_lower w z (Ne.symm hzw))

/-- The spherical correction in the first example, specialized from the
uniform descending correction and its proved contribution margins. -/
theorem origin_multiplicity :
    T.kl.canonical.repr (W.raw (m := 2)) (AffinePermutation.longest 5) =
      CanonicalCorrection.correction 2 := by
  have hactual := CanonicalRowSum.full_residual_positive_of_coordinates (m := 2)
    T.kl W.longest W.parabolic (CanonicalSpherical.index 2)
    (CanonicalSpherical.correction_indexing 2)
    (fun r hr => W.full_coordinate (by decide : 2 ≤ 2) T r (by omega))
    (fun r hr s hs => W.full_transition (by decide : 2 ≤ 2) T s r (by omega) (by omega))
    (W.nonspherical_bound (by decide : 2 ≤ 2) T)
  simpa only [CanonicalSpherical.index_zero, Nat.sub_zero] using
    CanonicalRowSum.raw_full_correction (m := 2) T.kl W.longest W.parabolic
      (CanonicalSpherical.index 2) hactual 0 (by decide)

/-- Either strong packet has constant raw standard coefficient one. -/
theorem strong_standard_constant (w : AffinePermutation 5) (hs : Supported w)
    (hm : CanonicalSchur.DoubleMaximal T.coxeter (Family.output 2) (Family.source 2) w)
    (hr : (packetMatrix 2 w hs).rank = 1)
    (hp : Matches (packetMatrix 2 w hs) .strong ∨
      Matches (packetMatrix 2 w hs) .strongDual) :
    T.kl.standard.repr (W.raw (m := 2)) w 0 = 1 := by
  have hc := MainPacketCoordinate.raw_packet_coordinate (m := 2) T.kl W.longest W.parabolic
    (by decide : 2 ≤ 2) W.convolution W.lattice_flags W.coordinates W.matrix_lengths
    W.block_lengths W.finite_longest w hs hm
  dsimp only at hc
  rw [(packetMatrix 2 w hs).raw_gap] at hc
  have hl : (packetMatrix 2 w hs).corank = 1 := by
    simp [PacketMatrix.corank, hr]
  have hcoeff (p : Polynomial ℤ) : normalize 4 p 0 = p.coeff 2 := by
    simpa using CanonicalGallery.normalized_coefficient 4 p 2
  rcases hp with hp | hp
  all_goals
    rw [hc, hl, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
    norm_num [a, s, beta, delta, CanonicalGallery.gap, CanonicalGallery.codimension]
    rw [hcoeff]
    norm_num [CanonicalGallery.count, CanonicalGallery.term0, CanonicalGallery.term1,
      CanonicalGallery.term2, CanonicalGallery.term3, CanonicalGallery.qInt,
      CanonicalGallery.qGauss, Gaussian.qInteger, Gaussian.qBinomial,
      Finset.sum_range_succ, Polynomial.coeff_add, Polynomial.coeff_mul]
    norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, show Int.toNat (2 : ℤ) = 2 from rfl,
      Gaussian.qBinomial, Polynomial.coeff_one, Polynomial.coeff_X]

end Guralnick.SeedDecomposition
