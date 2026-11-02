import Guralnick.FullFlagHeckeCounting
import Guralnick.PolynomialFullGalleryCardinality
import Guralnick.PolynomialCanonicalFullFlags

/-! # Deriving partial-flag convolution from the full-flag theorem

Only the full-flag orbit classification and binary Hecke convolution are
external. Full refinements, their fibers, the configuration bijection,
arbitrary-chain counting and all normalization factors are proved.
-/
noncomputable section
namespace Guralnick.PolynomialConvolutionConstruction
open Hecke ParabolicWeb CanonicalChains PolynomialsFromCounts
variable {n : ℕ} [NeZero n] {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)

/-- The old arbitrary-chain specialization interface is constructed, not
retained as a literature assumption. -/
def fromFullFlag
    (C : ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      FullFlagHeckeConvolution.Input K p hp) :
    PolynomialFlagConvolution.Input K D L where
  specialization := by
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    intro I J path source target w hpair
    let S := PolynomialCanonicalFullFlags.source (k := GaloisField p 2) c w
    let T := PolynomialCanonicalFullFlags.target (k := GaloisField p 2) (n := n)
    have hpos : FullFlagHeckeConvolution.RelativePosition T S w :=
      PolynomialCanonicalFullFlags.relativePosition c w
    have hnum := FullFlagHeckeConvolution.numerator_coordinate_count
      K p hp D L (C p hp) path S T w hpos
    have hcount := PolynomialFullGallery.fullGallery_card K D L p hp (C p hp) path S T
    have h := PolynomialConvolutionNormalization.normalized_raw_of_fullGallery_count
      D K L p hp path S T w hnum hcount
    obtain ⟨hs,ht⟩ := PolynomialCanonicalFullFlags.forget_pair c w source target hpair
    simpa only [S,T,hs,ht] using h

#print axioms fromFullFlag
end Guralnick.PolynomialConvolutionConstruction
