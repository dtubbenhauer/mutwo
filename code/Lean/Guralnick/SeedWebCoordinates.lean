import Guralnick.PolynomialWebLiterature
import Guralnick.WebGraphProof
import Guralnick.CanonicalAuxiliaryMargins
import Guralnick.GaussianExamples

/-!
# Actual web coordinates in the manuscript's first example

These are the source coordinates of the actual integral six-map morphism,
the actual retained-line morphism, and the corrected evaluated graph.
They specialize proved gallery formulas; the displayed polynomials are not
assumed evaluations. The only hypotheses are the general literature inputs.

These source evaluations are used by `SeedPolynomials` after the five-term
canonical expansion and rank-one correction are proved in separate files.
The corrected raw coordinate below is the aggregate coefficient, distinct
from the individual seed coefficient proved there.
-/

noncomputable section
open Polynomial
namespace Guralnick.SeedWebCoordinates

private theorem raw_polynomial : Gaussian.Y 2 =
    monomial 0 1 + monomial 1 4 + monomial 2 7 + monomial 3 7 +
      monomial 4 4 + monomial 5 1 := by
  norm_num [Gaussian.Y, Gaussian.qInteger, Gaussian.qBinomial,
    Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial]
  ring

private theorem raw_normalized : CanonicalFullCorrection.rawCoordinate 2 =
    (Finsupp.single (-1) 1 + Finsupp.single 1 4 + Finsupp.single 3 7 +
      Finsupp.single 5 7 + Finsupp.single 7 4 + Finsupp.single 9 1 :
        LaurentPolynomial ℤ) := by
  rw [CanonicalFullCorrection.rawCoordinate, raw_polynomial]
  simp only [Gaussian.normalize_add, Gaussian.normalize_monomial]
  norm_num [Gaussian.normalizationDegree]
  abel

variable (T : Hecke.Theory 5) (W : PolynomialWebLiterature T)

/-- The full first row of the manuscript's four-web coefficient table,
evaluated on the actual six-map Hecke element. -/
theorem raw_source :
    T.kl.standard.repr (ParabolicWeb.Family.raw (m := 2) T.kl W.longest W.parabolic)
      (AffinePermutation.longest 5) =
      Finsupp.single (-1) 1 + Finsupp.single 1 4 + Finsupp.single 3 7 +
        Finsupp.single 5 7 + Finsupp.single 7 4 + Finsupp.single 9 1 := by
  rw [MainSourceCoordinate.raw_source_coordinate (m := 2) T.kl W.longest W.parabolic
    (by decide : 2 ≤ 2) W.toWebLiterature.convolution W.lattice_flags
    W.block_lengths W.finite_longest]
  exact raw_normalized

/-- The retained-line web in the same table has coordinate `v³ + v⁵`.
Its definition is the integral split/merge composite, not this polynomial. -/
theorem one_line_source :
    T.kl.standard.repr
      (CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
        (1 : Fin 5) (2 : Fin 5)) (AffinePermutation.longest 5) =
      Finsupp.single 3 1 + Finsupp.single 5 1 := by
  rw [CanonicalAuxiliarySource.one_line_source_coordinate (by decide : 1 < 5)
    (1 : Fin 5) (2 : Fin 5) T.kl W.longest W.parabolic
    W.toWebLiterature.convolution W.lattice_flags (by decide) (by decide),
    FiniteAuxiliaryBlocks.oneLine_weight W.longest W.block_lengths (by decide)
      (1 : Fin 5) (2 : Fin 5) (by decide) (by decide) W.finite_longest]
  change normalize 5 (CanonicalGallery.qInt 2 * CanonicalGallery.qGauss 4 0) = _
  have hp : CanonicalGallery.qInt 2 * CanonicalGallery.qGauss 4 0 =
      monomial 0 1 + monomial 1 1 := by
    change Gaussian.qInteger 2 * Gaussian.qBinomial 4 0 = _
    norm_num [Gaussian.qInteger, Gaussian.qBinomial, Finset.sum_range_succ,
      ← C_mul_X_pow_eq_monomial]
  rw [hp, Gaussian.normalize_add, Gaussian.normalize_monomial,
    Gaussian.normalize_monomial]
  norm_num
  abel

/-- Reflection reverses the residue order and winding, fixes the source
`w₀`, and gives the same coordinate for the second auxiliary row. -/
theorem reflected_one_line_source :
    T.kl.standard.repr
      (ElementaryCoxeterDiagram.diagramMap T.kl (AffineReflection.equiv 5)
        (CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
          (1 : Fin 5) (2 : Fin 5))) (AffinePermutation.longest 5) =
      Finsupp.single 3 1 + Finsupp.single 5 1 := by
  have h := ElementaryCoxeterDiagram.diagramMap_coordinate T.kl
    (AffineReflection.equiv 5)
    (CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
      (1 : Fin 5) (2 : Fin 5)) (AffinePermutation.longest 5)
  have hw : (AffineReflection.equiv 5) (AffinePermutation.longest 5) =
      AffinePermutation.longest 5 := AffineReflection.reflect_longest 5
  rw [hw] at h
  exact h.trans (one_line_source T W)

/-- The actual corrected graph has aggregate source coordinate
`3v + 7v³ + 7v⁵ + 4v⁷ + v⁹`, as in the manuscript. -/
theorem corrected_graph_source :
    T.kl.standard.repr
      (WebProof.graphCorrected (by decide : 2 ≤ 2) T W.toWebLiterature)
      (AffinePermutation.longest 5) =
      Finsupp.single 1 3 + Finsupp.single 3 7 + Finsupp.single 5 7 +
        Finsupp.single 7 4 + Finsupp.single 9 1 := by
  rw [WebProof.graph_corrected_source (m := 2) (by decide) T W.toWebLiterature,
    CanonicalFullCorrection.proposed_residual]
  convert Gaussian.normalized_Q_two using 1

end Guralnick.SeedWebCoordinates
