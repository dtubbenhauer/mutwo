import Guralnick.MainGalleryCount
import Guralnick.CanonicalFullCorrection
import Guralnick.FiniteBlocks
import Guralnick.FiniteFlagEnumeration
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The actual raw source coefficient

The coefficient at the fixed ordinary finite longest element is obtained
from actual Laurent-lattice galleries, the proved original six-map count,
and the generic normalized convolution theorem. Prime-square evaluations
are converted to a Laurent identity by the proved interpolation theorem.
Finite-vector-space enumeration and the actual lattice-theory bundle are
both constructed. No source count formula is assumed.
-/

noncomputable section
namespace Guralnick

/-- Empty compatibility bundle: lattice theory and finite flag counts
are proved, so this historical interface imposes no hypotheses. -/
structure GeneralLatticeFlagInput : Prop where

theorem GeneralLatticeFlagInput.proved : GeneralLatticeFlagInput := ⟨⟩

theorem GeneralLatticeFlagInput.finite_flag_counts (_G : GeneralLatticeFlagInput)
    (k V : Type) [Field k] [Finite k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Finite V] : GalleryCounting.FiniteFlagCounts k V :=
  FiniteFlagEnumeration.provedFiniteFlagCounts k V

/-- Compatibility with the former input API. The lattice facts are proved
independently, without using the retained finite-flag input argument. -/
theorem GeneralLatticeFlagInput.lattice_theory (_G : GeneralLatticeFlagInput)
    (k : Type) [Field k] (n : ℕ) : LaurentLattice.Theory k n :=
  LaurentLattice.provedTheory k n

namespace MainSourceCoordinate
open Hecke ParabolicWeb CanonicalChains LatticeFlags

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)

/-- The exact main-word exponent at the fixed trivial-source index. -/
theorem source_exponent (hm : 2 ≤ m) (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    Chain.weight D (mainChain m) - c.system.length (AffinePermutation.longest (2*m+1)) =
      Gaussian.normalizationDegree m := by
  rw [FiniteBlocks.Family.main_weight, FiniteBlocks.Family.cost_eq hm D hblocks,
    FiniteBlocks.Family.source_eq_standard, hsource]
  unfold Gaussian.normalizationDegree
  ring

/-- The fixed-source gallery count over every prime-square field, in the
rational coefficient convention needed for Laurent specialization. -/
theorem prime_square_source_count (hm : 2 ≤ m) (G : GeneralLatticeFlagInput)
    (p : ℕ) (hp : p.Prime) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (source : Flag (GaloisField p 2) (2*m+1) (retained (Family.source m)))
      (target : Flag (GaloisField p 2) (2*m+1) (retained (Family.output m))),
      AffineLatticePosition.RelativePosition (GaloisField p 2) (2*m+1) target source
        (AffinePermutation.longest (2*m+1)) →
      (Nat.card (FlagConvolution.Gallery (GaloisField p 2) (mainChain m) source target) : ℚ) =
        Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2) (Gaussian.Y m) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (2*m+1) := ⟨by omega⟩
  intro source target hpos
  let T := G.lattice_theory (GaloisField p 2) (2*m+1)
  letI := T.period_finite (LatticeFlags.Family.targetNode target)
  letI : Finite (MainGalleryCount.Space target) := Module.finite_of_finite (GaloisField p 2)
  have heq : LatticeFlags.Family.sourceNode source = LatticeFlags.Family.targetNode target := by
    exact (AffineLatticePosition.relativePosition_longest_zero_nodes_eq (GaloisField p 2)
      (2*m+1) hpos
      ((LatticeFlags.Family.output_mem m 0).mpr (Or.inl rfl))
      ((LatticeFlags.Family.source_mem m 0).mpr rfl)).symm
  have hc := MainGalleryCount.main_source_gallery_count hm T
    (G.finite_flag_counts (GaloisField p 2) (MainGalleryCount.Space target)) heq
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  have hcard : Nat.card (GaloisField p 2) = p^2 := GaloisField.card p 2 (by decide)
  rw [hcard] at hq
  have heval := Polynomial.eval₂_at_apply (p := Gaussian.Y m)
    (Int.castRingHom ℚ) ((p^2 : ℕ) : ℤ)
  simp only [Int.coe_castRingHom, Int.cast_natCast, Nat.cast_pow] at heval hq
  exact hq.trans heval.symm

/-- The actual standard coefficient of the integral raw web at w₀ is the
rawCoordinate used by the canonical-correction proof. This is a theorem
from generic cited frameworks and original proved gallery arguments. -/
theorem raw_source_coordinate (hm : 2 ≤ m) (C : FlagConvolution.Input K D L)
    (G : GeneralLatticeFlagInput) (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    K.standard.repr (Family.raw K D L) (AffinePermutation.longest (2*m+1)) =
      CanonicalFullCorrection.rawCoordinate m := by
  rw [main_raw_eq_chain K D L]
  have hc := FlagConvolution.coordinate_of_uniform_count K D L C (mainChain m)
    (AffinePermutation.longest (2*m+1)) (Gaussian.Y m)
    (prime_square_source_count hm G)
  rw [source_exponent D hm hblocks hsource] at hc
  exact hc

end MainSourceCoordinate
end Guralnick
