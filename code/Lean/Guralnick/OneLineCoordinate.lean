import Guralnick.OneLineOrbit
import Guralnick.CanonicalTwoRowWindow
import Guralnick.MainPacketCoordinate

/-! # Exact standard coordinates of the actual one-line web

The signed Gaussian indices include the empty-rank cases. Actual finite
lattice galleries, their quotient ranks, and residue counts are assembled
before invoking the general normalized convolution dictionary.
-/
noncomputable section
namespace Guralnick.OneLineCoordinate
open LaurentLattice LatticeFlags CanonicalChains CanonicalFlagAuxiliary CanonicalOneLineFlags
open AffineLatticePosition OrbitMatrix WindowPacketMatrix MainPacketCoordinate

variable {m : ℕ} {k : Type} [Field k]

theorem count_from_position [Finite k] (hn : 1<2*m+1)
    (j f : Fin (2*m+1)) (hj : 1≤j.val) (hf : 1≤f.val)
    (source : Flag k (2*m+1) (retained (src hn)))
    (target : Flag k (2*m+1) (retained (out hn f)))
    [FiniteDimensional k (quotientSpace (targetBase hn f target))]
    [Finite (quotientSpace (targetBase hn f target))]
    (T : Theory k (2*m+1)) (input : CoordinateDimensionInput k (2*m+1))
    (hcount : GalleryCounting.FiniteFlagCounts k (quotientSpace (targetBase hn f target)))
    (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hpos : RelativePosition k (2*m+1) target source w) :
    let A := CanonicalTwoRowWindow.matrix f w hs
    (Nat.card (FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ)
        (CanonicalAuxiliary.oneLineCount A.n ((j.val : ℤ)-A.rank) A.d A.a A.b) := by
  let A := CanonicalTwoRowWindow.matrix f w hs
  let C := OneLineOrbit.coordinates hn f source target hpos
  let h := C.bounds input hs
  have hr : A.rank ≤ 2*m+1 := by have hh := A.rank_bound (Nat.le_of_lt f.isLt); omega
  exact OneLineOrbit.one_line_count_of_cumulative C input h j hj hf T hcount A.rank hr A.a A.b
    (CanonicalTwoRowWindow.cumulative_rank f w hs)
    (CanonicalTwoRowWindow.cumulative_corank f w hs)
    (CanonicalTwoRowWindow.cumulative_a f w hs)
    (CanonicalTwoRowWindow.cumulative_c f w hs)

variable {c : Hecke.WindowCoxeter (2*m+1)} (K : Hecke.KLRealization c)
  (D : ∀ I : ParabolicWeb.Index (2*m+1), ParabolicWeb.LongestData c I)
  (L : ParabolicWeb.Laws K D)

theorem prime_square_count (hn : 1<2*m+1) (j f : Fin (2*m+1))
    (hj : 1≤j.val) (hf : 1≤f.val) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (p : ℕ) (hp : p.Prime) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (source : Flag (GaloisField p 2) (2*m+1) (retained (src hn)))
      (target : Flag (GaloisField p 2) (2*m+1) (retained (out hn f))),
      RelativePosition (GaloisField p 2) (2*m+1) target source w →
      (Nat.card (FlagConvolution.Gallery (GaloisField p 2)
        (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target) : ℚ) =
        Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2)
          (let A := CanonicalTwoRowWindow.matrix f w hs
           CanonicalAuxiliary.oneLineCount A.n ((j.val : ℤ)-A.rank) A.d A.a A.b) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro source target hpos
  let T := G.lattice_theory (GaloisField p 2) (2*m+1)
  letI := T.period_finite (targetBase hn f target)
  letI : Finite (quotientSpace (targetBase hn f target)) := Module.finite_of_finite (GaloisField p 2)
  have hc := count_from_position hn j f hj hf source target T (O (GaloisField p 2))
    (G.finite_flag_counts (GaloisField p 2) (quotientSpace (targetBase hn f target))) w hs hpos
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  have hcard : Nat.card (GaloisField p 2) = p^2 := GaloisField.card p 2 (by decide)
  rw [hcard] at hq
  let A := CanonicalTwoRowWindow.matrix f w hs
  have heval := Polynomial.eval₂_at_apply
    (p := CanonicalAuxiliary.oneLineCount A.n ((j.val : ℤ)-A.rank) A.d A.a A.b)
    (Int.castRingHom ℚ) ((p^2 : ℕ) : ℤ)
  simp only [Int.coe_castRingHom,Int.cast_natCast,Nat.cast_pow] at heval hq
  exact hq.trans heval.symm

/-- Exact raw standard coordinate at any supported actual window, including
nonmaximal representatives of the coarse output double coset. -/
theorem raw_coordinate (hn : 1<2*m+1) (j f : Fin (2*m+1))
    (hj : 1≤j.val) (hf : 1≤f.val)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    let A := CanonicalTwoRowWindow.matrix f w hs
    K.standard.repr (oneLine K D L (Nat.zero_lt_of_lt hn) j f) w =
      normalize (Chain.weight D (oneLineChain (Nat.zero_lt_of_lt hn) j f)-c.system.length w)
        (CanonicalAuxiliary.oneLineCount A.n ((j.val : ℤ)-A.rank) A.d A.a A.b) := by
  rw [oneLine_eq_chain K D L]
  exact FlagConvolution.coordinate_of_uniform_count K D L C
    (oneLineChain (Nat.zero_lt_of_lt hn) j f) w _
    (prime_square_count hn j f hj hf G O w hs)

/-- At a genuine coarse maximal index the computed exponent is the
one-line length-gap polynomial, with all indexing conditions explicit. -/
theorem maximal_coordinate (hn : 1<2*m+1) (j f : Fin (2*m+1))
    (hj : 1≤j.val) (hf : 1≤f.val)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (Q : ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D) (hsource : FiniteBlocks.StandardFiniteLongestInput D)
    (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (hw : CanonicalSchur.DoubleMaximal c (twoRow (Nat.zero_lt_of_lt hn) f)
      (CanonicalChains.source (Nat.zero_lt_of_lt hn)) w) :
    let A := CanonicalTwoRowWindow.matrix f w hs
    K.standard.repr (oneLine K D L (Nat.zero_lt_of_lt hn) j f) w =
      normalize (CanonicalOneLine.lengthGap A.n ((j.val : ℤ)-A.rank) A.d A.a A.b)
        (CanonicalAuxiliary.oneLineCount A.n ((j.val : ℤ)-A.rank) A.d A.a A.b) := by
  rw [raw_coordinate K D L hn j f hj hf C G O w hs]
  rw [CanonicalTwoRowWindow.actual_normalization D Q hblocks hsource j f hj hf w hs hw]

/-- Actual nonzero support supplies both bounded winding and the rank
inequality needed for the one-line canonical degree test. -/
theorem support_and_rank (hn : 1<2*m+1) (j f : Fin (2*m+1))
    (hj : 1≤j.val) (hf : 1≤f.val)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1)) (w : AffinePermutation (2*m+1))
    (hne : K.standard.repr (oneLine K D L (Nat.zero_lt_of_lt hn) j f) w ≠ 0) :
    ∃ hs : Supported w, (CanonicalTwoRowWindow.matrix f w hs).rank ≤ j.val := by
  rw [oneLine_eq_chain K D L] at hne
  obtain ⟨p,hp,hgal⟩ := FlagConvolution.nonempty_gallery_of_nonzero K D L C
    (oneLineChain (Nat.zero_lt_of_lt hn) j f) w hne
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨source,target,hpos,hg⟩ := hgal
  let T := G.lattice_theory (GaloisField p 2) (2*m+1)
  let coords := OneLineOrbit.coordinates hn f source target hpos
  let hs := OneLineOrbit.supported_of_nonempty coords (O (GaloisField p 2)) j hj hf T hg
  refine ⟨hs,?_⟩
  rw [← CanonicalTwoRowWindow.cumulative_rank f w hs]
  exact OneLineOrbit.rank_le_of_nonempty coords (O (GaloisField p 2))
    (coords.bounds (O (GaloisField p 2)) hs) j hj hf T hg

end Guralnick.OneLineCoordinate
