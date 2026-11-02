import Guralnick.MainPacketCoordinate
import Guralnick.CanonicalApplication

/-! # Actual canonical support of the main web

Cleared positivity first prevents a nonzero canonical coordinate from
vanishing in the standard coordinate. Actual galleries then force bounded
winding support, and the proved normalized count gives the six positions.
-/
noncomputable section
namespace Guralnick.MainCanonicalSupport
open Hecke ParabolicWeb CanonicalSchur MainPacketCoordinate
open WindowPacketMatrix OrbitMatrix

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
  (P : PositivityInput K)

include P

theorem standard_ne_zero_of_canonical_ne_zero (w : AffinePermutation (2*m+1))
    (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    K.standard.repr (Family.raw K D L) w ≠ 0 := by
  intro hz
  exact hne (canonical_eq_zero_of_standard_zero K P (Family.denominator_ne_zero K D L)
    (Family.raw K D L) (Family.raw_cleared_nonnegative K D L P) w hz)

theorem supported_of_canonical_ne_zero (hm : 2 ≤ m)
    (C : FlagConvolution.Input K D L) (O : CoordinateInput (2*m+1))
    (w : AffinePermutation (2*m+1)) (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    Supported w :=
  supported_of_standard_ne_zero K D L hm C O w
    (standard_ne_zero_of_canonical_ne_zero K D L P w hne)

/-- Complete six-position support in the actual affine Hecke algebra.
Every hypothesis is a generic cited framework; the original main count,
its exponent, the packet margins and degree inequalities are proved. -/
theorem raw_six_position_support (hm : 2 ≤ m)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (Q : ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D) (S : Compatibility K)
    (w : AffinePermutation (2*m+1)) (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    ∃ hs : Supported w,
      let A := packetMatrix m w hs
      DegreeBounds.SixPositions A.beta A.delta A.a A.s := by
  let hs := supported_of_canonical_ne_zero K D L P hm C O w hne
  refine ⟨hs,?_⟩
  exact CanonicalApplication.raw_packet_support K D L P w (packetMatrix m w hs)
    (raw_packet_coordinate K D L hm C G O Q hblocks hsource w hs
      (raw_doubleMaximal K D L S w hne)) hne

/-- At corank zero the canonical support lies in the marked family matrix,
with the exact boundary behavior proved in the original gallery count. -/
theorem raw_boundary_support (hm : 2 ≤ m)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (Q : ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D) (S : Compatibility K)
    (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hz : (packetMatrix m w hs).corank = 0)
    (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    (packetMatrix m w hs).entries = Guralnick.Family.prescribedArray m m := by
  exact CanonicalApplication.raw_packet_boundary K D L P w (packetMatrix m w hs) hz
    (raw_packet_coordinate K D L hm C G O Q hblocks hsource w hs
      (raw_doubleMaximal K D L S w hne)) hne

end Guralnick.MainCanonicalSupport
