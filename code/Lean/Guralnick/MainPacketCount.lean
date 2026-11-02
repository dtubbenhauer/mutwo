import Guralnick.MainOrbitRanks
import Guralnick.PacketCumulative

/-! # The actual four-case main count with all orbit ranks discharged

The input affine window determines a genuine packet matrix. Every
intersection dimension in the finite-gallery count is now derived from
actual lattice coordinates and proved residue counts. The original
four-case count is a conclusion, uniformly in all supported endpoints.
-/
noncomputable section
namespace Guralnick.OrbitMatrix
open LaurentLattice AffineLatticePosition LatticeGallery
open LatticeFlags LatticeFlags.Family MainGalleryCount WindowPacketMatrix

variable {k : Type} [Field k] {m : ℕ}
  {source : Flag k (2*m+1) (S m)} {target : Flag k (2*m+1) (O m)}
  {w : AffinePermutation (2*m+1)}

private theorem cumulative_zero (b : ℕ) (hb : b ≤ 2*m+1) :
    cumulativeCount (2*m+1) w 0 b 0 = prefixCount w b 0 := by
  simpa only [mul_zero] using cumulative_eq_prefix w b hb 0

private theorem cumulative_one (b : ℕ) (hb : b ≤ 2*m+1) :
    cumulativeCount (2*m+1) w 0 b (2*m+1 : ℕ) = prefixCount w b 1 := by
  simpa only [mul_one] using cumulative_eq_prefix w b hb 1

/-- No special intersection dimensions are assumed: they are derived from
the actual relative position, generic coordinate theory, and finite counts. -/
theorem main_count_from_position [Finite k]
    [FiniteDimensional k (Space target)] [Finite (Space target)]
    (hm : 2 ≤ m) (T : Theory k (2*m+1))
    (input : CoordinateDimensionInput k (2*m+1))
    (hcount : GalleryCounting.FiniteFlagCounts k (Space target))
    (hpos : RelativePosition k (2*m+1) target source w) (hs : Supported w) :
    let A := packetMatrix m w hs
    (Nat.card (FlagConvolution.Gallery k (CanonicalChains.mainChain m) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ)
        (CanonicalGallery.count A.corank A.a A.s A.beta A.delta) := by
  let A := packetMatrix m w hs
  let C := mainCoordinates k hm hpos
  let h := C.bounds_of_inverse_winding hm input hs
  have hI : Module.finrank k (lower h) = A.rank := by
    rw [lower_rank_cumulative hm C h input,cumulative_zero _ le_rfl,prefix_N_zero m w hs]
    rfl
  have hK : Module.finrank k (upperFlag h) = 2*m+1-A.rank := by
    rw [upper_rank_cumulative hm C h input,cumulative_one _ le_rfl,prefix_N_one m w hs]
    rfl
  have haN : Module.finrank k (lower h ⊓ flagF hm target : Submodule k (Space target)) =
      entries m w 0 0 := by
    unfold lower flagF
    rw [lower_intersection_rank_cumulative hm C h input (endpointF hm) m (by omega) C.middle,
      cumulative_zero _ (by omega),prefix_m_zero m w hs]
  have hbN : Module.finrank k (lower h ⊓ flagF' hm target : Submodule k (Space target)) =
      entries m w 0 0 + entries m w 1 0 := by
    unfold lower flagF'
    rw [lower_intersection_rank_cumulative hm C h input (endpointF' hm) (m+1) (by omega) C.next,
      cumulative_zero _ (by omega),prefix_middle_zero m w hs]
  have hcN : Module.finrank k (upperFlag h ⊓ flagF hm target : Submodule k (Space target)) =
      entries m w 0 0 + entries m w 0 1 := by
    unfold upperFlag flagF
    rw [upper_intersection_rank_cumulative hm C h input (endpointF hm) m (by omega) C.middle,
      cumulative_one _ (by omega),prefix_m_one m w hs]
  have hdN : Module.finrank k (upperFlag h ⊓ flagF' hm target : Submodule k (Space target)) =
      entries m w 0 0 + entries m w 0 1 + entries m w 1 0 + entries m w 1 1 := by
    unfold upperFlag flagF'
    rw [upper_intersection_rank_cumulative hm C h input (endpointF' hm) (m+1) (by omega) C.next,
      cumulative_one _ (by omega),prefix_middle_one m w hs]
  have hrow := A.first_row
  have hcols := A.outer_columns
  have hr := A.rank_le
  have ha : (Module.finrank k (lower h ⊓ flagF hm target : Submodule k (Space target)) : ℤ) = A.a := by
    rw [haN]
    rfl
  have hb : (Module.finrank k (lower h ⊓ flagF' hm target : Submodule k (Space target)) : ℤ) = A.a+A.beta := by
    rw [hbN,Nat.cast_add]
    rfl
  have hc : (Module.finrank k (upperFlag h ⊓ flagF hm target : Submodule k (Space target)) : ℤ) =
      (m-A.rank : ℕ)+A.s := by
    rw [hcN,Nat.cast_add]
    unfold CanonicalMatrix.PacketMatrix.s
    change A.entries 0 0+A.entries 0 1+A.entries 0 2=m at hrow
    change A.entries 0 0+A.entries 1 0+A.entries 2 0 =
      A.entries 0 2+A.entries 1 2+A.entries 2 2 at hcols
    change (A.entries 0 0 : ℤ)+A.entries 0 1 = _
    unfold CanonicalMatrix.PacketMatrix.rank at *
    omega
  have hd : (Module.finrank k (upperFlag h ⊓ flagF' hm target : Submodule k (Space target)) : ℤ) =
      (m-A.rank : ℕ)+A.s+A.delta := by
    rw [hdN]
    push_cast
    change (A.entries 0 0 : ℤ)+A.entries 0 1+A.entries 1 0+A.entries 1 1 = _
    have hcc : (A.entries 0 0 : ℤ)+A.entries 0 1 = (m-A.rank : ℕ)+A.s := by
      simpa only [hcN,Nat.cast_add] using hc
    rw [hcc]
    unfold CanonicalMatrix.PacketMatrix.delta
    ring
  have hh := main_gallery_count hm T h hcount (r := A.rank) (l := m-A.rank)
    (a := A.a) (s := A.s) (β := A.beta) (δ := A.delta)
    (by omega) hI hK ha hb hc hd
  have he : ((m-A.rank : ℕ) : ℤ) = A.corank := by
    rw [Int.ofNat_sub hr]
    rfl
  simpa only [he] using hh

end Guralnick.OrbitMatrix
