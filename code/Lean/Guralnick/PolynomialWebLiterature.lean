import Guralnick.WebLiterature
import Guralnick.CanonicalSchurFromRefinement
import Guralnick.PolynomialConvolutionConstruction
import Guralnick.PolynomialOrbitTransfer
import Guralnick.PolynomialOrbitCounting
import Guralnick.ElementaryCoxeterParabolic
import Guralnick.ElementaryCoxeterFinite
import Guralnick.ElementaryCoxeterDiagram
import Guralnick.OrbitDimensionLength
import Guralnick.ElementaryCoxeterBlockLength
import Guralnick.ParabolicStandardSum
import Guralnick.ParabolicIdealInclusion

/-!
# Literature inputs in the original polynomial-lattice model

The geometric framework fields are now stated on independent polynomial
Laurent lattices, matching the source model. Every completion, degree,
cyclic-flag, gallery, and orbit-quotient conversion to the manuscript's
completed model is proved by `toWebLiterature`.

Only full-flag orbit classification and binary Hecke convolution remain
external on the geometric side. Actual full refinements, their cardinalities,
the full-to-partial configuration bijection and the entire chain
normalization are proved by `PolynomialConvolutionConstruction`.
-/
noncomputable section
namespace Guralnick

/-- The actual finite subgroups and their longest elements are constructed
from the affine windows, before any external Schur theorem is supplied. -/
abbrev polynomialLongest {n : ℕ} (T : Hecke.Theory n) :=
  ElementaryCoxeterParabolic.longestData T.coxeter

/-- Historical statement name; the inclusion is proved below. -/
def PolynomialParabolicInclusion {n : ℕ} (T : Hecke.Theory n) : Prop :=
  ∀ I J : ParabolicWeb.Index n, I.val ⊆ J.val →
    SphericalMaps.spherical (ParabolicWeb.symmetrizer T.kl (polynomialLongest T) J) ≤
      SphericalMaps.spherical (ParabolicWeb.symmetrizer T.kl (polynomialLongest T) I)

def polynomialParabolic {n : ℕ} (T : Hecke.Theory n)
    (C : CanonicalSchur.Compatibility T.kl) :
    ParabolicWeb.Laws T.kl (polynomialLongest T) where
  standard_sum I := ParabolicStandardSum.standard_sum T.kl C I (polynomialLongest T I)
  inclusion := ParabolicIdealInclusion.inclusion T.kl C (polynomialLongest T)

structure PolynomialWebLiterature {n : ℕ} [NeZero n] (T : Hecke.Theory n) where
  refinement : CanonicalRefinement.StandardCompatibility T.kl (polynomialLongest T)
  full_flag : ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    FullFlagHeckeConvolution.Input T.kl p hp

namespace PolynomialWebLiterature
variable {n : ℕ} [NeZero n] {T : Hecke.Theory n}

abbrev longest (_W : PolynomialWebLiterature T) := polynomialLongest T

/-- The one canonical-to-standard Schur theorem already implies the
canonical-support theorem, by elementary eigenvector triangularity. -/
def schur (W : PolynomialWebLiterature T) : CanonicalSchur.Compatibility T.kl :=
  CanonicalSchurFromRefinement.toCompatibility T.kl W.longest W.refinement

def parabolic (W : PolynomialWebLiterature T) : ParabolicWeb.Laws T.kl W.longest :=
  polynomialParabolic T W.schur

/-- The complete partial-gallery formula is derived from binary full-flag convolution. -/
def convolution (W : PolynomialWebLiterature T) :
    PolynomialFlagConvolution.Input T.kl W.longest W.parabolic :=
  PolynomialConvolutionConstruction.fromFullFlag T.kl W.longest W.parabolic W.full_flag

theorem parabolic_inclusion (W : PolynomialWebLiterature T) : PolynomialParabolicInclusion T :=
  ParabolicIdealInclusion.inclusion T.kl W.schur W.longest

theorem lattice_flags (_W : PolynomialWebLiterature T) : GeneralLatticeFlagInput :=
  GeneralLatticeFlagInput.proved

def coordinates (_W : PolynomialWebLiterature T) (k : Type) [Field k] :
    PolynomialOrbitCoordinates.Input k n := PolynomialOrbitCounting.provedInput k n

theorem matrix_dimension (_W : PolynomialWebLiterature T) :
    OrbitMatrixElementary.DimensionLengthInput T.coxeter :=
  OrbitDimensionLength.dimensionLength T.coxeter

def matrix_lengths (_W : PolynomialWebLiterature T) :
    OrbitMatrix.ThreeColumnLengthInput T.coxeter :=
  OrbitDimensionLength.threeColumnLength T.coxeter

theorem block_lengths (W : PolynomialWebLiterature T) :
    FiniteBlocks.BlockLengthInput W.longest :=
  ElementaryCoxeterBlockLength.blockLength T.coxeter W.longest

theorem finite_longest (W : PolynomialWebLiterature T) :
    FiniteBlocks.StandardFiniteLongestInput W.longest :=
  ElementaryCoxeterFinite.standardFiniteLongest T.coxeter W.longest

theorem diagram_invariance (_W : PolynomialWebLiterature T) :
    AffineReflection.DiagramInvarianceInput T.kl :=
  ElementaryCoxeterDiagram.diagramInvariance T.kl
end PolynomialWebLiterature

/-- The original proof's entire geometric interface is supplied by proved
comparison maps from the cited polynomial model. -/
def PolynomialWebLiterature.toWebLiterature {n : ℕ} [NeZero n] {T : Hecke.Theory n}
    (W : PolynomialWebLiterature T) : WebLiterature T where
  longest := W.longest
  parabolic := W.parabolic
  schur := W.schur
  refinement := W.refinement
  convolution := PolynomialFlagConvolution.Input.toCompleted T.kl W.longest W.parabolic W.convolution
  lattice_flags := W.lattice_flags
  coordinates := fun k _ => PolynomialOrbitCoordinates.Input.toCompleted k n (W.coordinates k)
  matrix_lengths := W.matrix_lengths
  block_lengths := W.block_lengths
  finite_longest := W.finite_longest
  diagram_invariance := W.diagram_invariance

#print axioms PolynomialWebLiterature.toWebLiterature
end Guralnick
