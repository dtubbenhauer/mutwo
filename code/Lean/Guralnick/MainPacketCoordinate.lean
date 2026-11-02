import Guralnick.MainPacketCount
import Guralnick.MainSourceCoordinate
import Guralnick.OrbitLengthInput

/-!
# The actual raw web coordinate at every supported maximal endpoint

The full four-case polynomial and its normalization are derived from
actual Laurent-lattice galleries, proved finite counts, and the general
periodic Schur dictionary. No original raw coefficient formula is an input.
-/
noncomputable section
namespace Guralnick.MainPacketCoordinate
open Hecke ParabolicWeb CanonicalChains LatticeFlags
open OrbitMatrix WindowPacketMatrix

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)

/-- Only the general coordinate theorem, over arbitrary fields, is supplied
here. No original main-family endpoint or count is in this input. -/
def CoordinateInput (N : ℕ) [NeZero N] : Prop :=
  ∀ (k : Type) [Field k], CoordinateDimensionInput k N

/-- A nonzero actual raw standard coefficient forces the three-column
support, by transporting a nonempty convolution gallery to its endpoint
lattice containments. -/
theorem supported_of_standard_ne_zero (hm : 2 ≤ m)
    (C : FlagConvolution.Input K D L) (O : CoordinateInput (2*m+1))
    (w : AffinePermutation (2*m+1))
    (hne : K.standard.repr (Family.raw K D L) w ≠ 0) : Supported w := by
  rw [main_raw_eq_chain K D L] at hne
  obtain ⟨p,hp,hgal⟩ := FlagConvolution.nonempty_gallery_of_nonzero K D L C
    (mainChain m) w hne
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨source,target,hpos,⟨gallery⟩⟩ := hgal
  let g := FlagConvolution.mainGalleryEquiv source target gallery
  exact bounds_inverse_winding hm (mainCoordinates (GaloisField p 2) hm hpos)
    (g.bounds hm) (O (GaloisField p 2))

/-- The generic dimension/length dictionary fixes the exact exponent,
including the prescribed lower source w₀ and the six-map normalization. -/
theorem packet_exponent (hm : 2 ≤ m) (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D)
    (Q : ThreeColumnLengthInput c) (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hw : CanonicalSchur.DoubleMaximal c (Family.output m) (Family.source m) w) :
    Chain.weight D (mainChain m) - c.system.length w =
      (2*(m : ℤ)^2+2*m-3) -
        PeriodicMatrix.dimension (fun i j => ((packetMatrix m w hs).entries i j : ℤ)) := by
  have hw' : CanonicalSchur.DoubleMaximal c (FiniteBlocks.Family.output hm).index
      (source (NeZero.pos (2*m+1))) w := by
    rw [FiniteBlocks.Family.output_index,← FiniteBlocks.Family.source_eq_standard]
    exact hw
  have hd := Q.dimension_length (FiniteBlocks.Family.output hm) rfl w hs hw'
  have he : (fun i j => (compositionEntries (FiniteBlocks.Family.output hm) w i j : ℤ)) =
      (fun i j => ((packetMatrix m w hs).entries i j : ℤ)) := by
    funext i j
    rw [compositionEntries_output]
    rfl
  rw [he] at hd
  have hc := MainSourceCoordinate.source_exponent D hm hblocks hsource
  unfold Gaussian.normalizationDegree at hc
  linarith

/-- The original finite count over the prime-square fields used by
Laurent interpolation, with all six orbit ranks already proved. -/
theorem prime_square_packet_count (hm : 2 ≤ m) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (p : ℕ) (hp : p.Prime) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (source : Flag (GaloisField p 2) (2*m+1) (retained (Family.source m)))
      (target : Flag (GaloisField p 2) (2*m+1) (retained (Family.output m))),
      AffineLatticePosition.RelativePosition (GaloisField p 2) (2*m+1) target source w →
      (Nat.card (FlagConvolution.Gallery (GaloisField p 2) (mainChain m) source target) : ℚ) =
        Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2)
          (let A := packetMatrix m w hs
           CanonicalGallery.count A.corank A.a A.s A.beta A.delta) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro source target hpos
  let T := G.lattice_theory (GaloisField p 2) (2*m+1)
  letI := T.period_finite (LatticeFlags.Family.targetNode target)
  letI : Finite (MainGalleryCount.Space target) := Module.finite_of_finite (GaloisField p 2)
  have hc := main_count_from_position hm T (O (GaloisField p 2))
    (G.finite_flag_counts (GaloisField p 2) (MainGalleryCount.Space target)) hpos hs
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  have hcard : Nat.card (GaloisField p 2) = p^2 := GaloisField.card p 2 (by decide)
  rw [hcard] at hq
  let A := packetMatrix m w hs
  have heval := Polynomial.eval₂_at_apply
    (p := CanonicalGallery.count A.corank A.a A.s A.beta A.delta)
    (Int.castRingHom ℚ) ((p^2 : ℕ) : ℤ)
  simp only [Int.coe_castRingHom,Int.cast_natCast,Nat.cast_pow] at heval hq
  exact hq.trans heval.symm

/-- The precise standard-coordinate identity needed by the manuscript's
canonical support argument, now proved from generic cited frameworks. -/
theorem raw_packet_coordinate (hm : 2 ≤ m) (C : FlagConvolution.Input K D L)
    (G : GeneralLatticeFlagInput) (O : CoordinateInput (2*m+1))
    (Q : ThreeColumnLengthInput c) (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D)
    (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hw : CanonicalSchur.DoubleMaximal c (Family.output m) (Family.source m) w) :
    let A := packetMatrix m w hs
    K.standard.repr (Family.raw K D L) w =
      normalize ((2*(m : ℤ)^2+2*m-3)-PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)))
        (CanonicalGallery.count A.corank A.a A.s A.beta A.delta) := by
  rw [main_raw_eq_chain K D L]
  have hc := FlagConvolution.coordinate_of_uniform_count K D L C (mainChain m) w
    (let A := packetMatrix m w hs
     CanonicalGallery.count A.corank A.a A.s A.beta A.delta)
    (prime_square_packet_count hm G O w hs)
  rw [packet_exponent D hm hblocks hsource Q w hs hw] at hc
  exact hc

end Guralnick.MainPacketCoordinate
