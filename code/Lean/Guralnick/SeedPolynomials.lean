import Guralnick.SeedRankOne
import Guralnick.SeedDecomposition
import Guralnick.SeedWebCoordinates
import Guralnick.FamilyPolynomialReadout

/-!
# The actual ordinary KL polynomials in the first example

These identifications use the canonical Hecke elements, their proved web
expansions, and the ordinary fixed-source KL normalization. The displayed
polynomials are conclusions, not assumptions or definitions of KL values.
-/

noncomputable section
namespace Guralnick.SeedPolynomials
open Polynomial

private theorem source_arithmetic :
    (Finsupp.single (-1) 1 + Finsupp.single 1 4 + Finsupp.single 3 7 +
      Finsupp.single 5 7 + Finsupp.single 7 4 + Finsupp.single 9 1 : LaurentPolynomial ℤ) =
    (Finsupp.single 1 2 + Finsupp.single 3 4 + Finsupp.single 5 5 +
      Finsupp.single 7 4 + Finsupp.single 9 1) +
      (Finsupp.single 1 1 + Finsupp.single 3 1) +
      (Finsupp.single 3 1 + Finsupp.single 5 1) +
      (Finsupp.single 3 1 + Finsupp.single 5 1) +
      (Finsupp.single 1 1 + Finsupp.single (-1) 1) := by
  change (Finsupp.single (-1) 1 + Finsupp.single 1 4 + Finsupp.single 3 7 +
    Finsupp.single 5 7 + Finsupp.single 7 4 + Finsupp.single 9 1 : ℤ →₀ ℤ) = _
  ext k
  simp only [AddMonoidAlgebra, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> norm_num

variable (T : Hecke.Theory 5) (W : PolynomialWebLiterature T)
include W

theorem rank_one_polynomial :
    T.kl.polynomial (AffinePermutation.longest 5)
      (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 1) (by decide : 1 ≤ 2)) =
      1 + X := by
  apply FamilyPolynomialReadout.of_source_coordinate
    (by decide : 2 ≤ 2) (by decide : 1 ≤ 1) (by decide : 1 ≤ 2)
  rw [SeedRankOne.canonical_source T W]
  change (Finsupp.single 1 1 + Finsupp.single 3 1 : LaurentPolynomial ℤ) =
    normalize 3 (1 + X)
  have hp : (1 + X : Polynomial ℤ) = monomial 0 1 + monomial 1 1 := by
    simp [Polynomial.monomial_one_one_eq_X]
  rw [hp, Gaussian.normalize_add, Gaussian.normalize_monomial, Gaussian.normalize_monomial]
  norm_num
  abel

theorem rank_one_mu :
    Hecke.familyMu (by decide : 2 ≤ 2) (by decide : 1 ≤ 1)
      (by decide : 1 ≤ 2) T.kl = 1 := by
  change (T.kl.polynomial (AffinePermutation.longest 5)
    (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 1)
      (by decide : 1 ≤ 2))).coeff 1 = 1
  rw [rank_one_polynomial T W]
  norm_num [Polynomial.coeff_one]

/-- The four-web subtraction in the paper holds as an equality of actual
Hecke elements, before any coordinate is read. -/
theorem four_web_identity :
    T.kl.canonical
      (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2)) =
      ParabolicWeb.Family.raw (m := 2) T.kl W.longest W.parabolic -
      SeedRankOne.raw T -
      CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
        (1 : Fin 5) (2 : Fin 5) -
      ElementaryCoxeterDiagram.diagramMap T.kl (AffineReflection.equiv 5)
        (CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
          (1 : Fin 5) (2 : Fin 5)) := by
  have h := SeedDecomposition.web_expansion T W
  change ParabolicWeb.Family.raw (m := 2) T.kl W.longest W.parabolic =
    T.kl.canonical
      (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2)) +
    T.kl.canonical SeedRankOne.endpoint + _ + _ + _ at h
  rw [← SeedRankOne.canonical_identity T W, SeedRankOne.corrected] at h
  rw [h]
  abel

/-- The full canonical-to-standard coefficient, with the prescribed
ordinary lower endpoint `w₀`, is obtained from the proved vector expansion. -/
theorem diagonal_source :
    T.kl.standard.repr
      (T.kl.canonical
        (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2)))
      (AffinePermutation.longest 5) =
      Finsupp.single 1 2 + Finsupp.single 3 4 + Finsupp.single 5 5 +
        Finsupp.single 7 4 + Finsupp.single 9 1 := by
  have h := congrArg
    (fun x => T.kl.standard.repr x (AffinePermutation.longest 5))
    (SeedDecomposition.web_expansion T W)
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, T.kl.canonical_diagonal, mul_one] at h
  rw [SeedWebCoordinates.raw_source T W, SeedWebCoordinates.one_line_source T W,
    SeedWebCoordinates.reflected_one_line_source T W] at h
  change _ = T.kl.standard.repr (T.kl.canonical
      (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2)))
      (AffinePermutation.longest 5) +
    T.kl.standard.repr (T.kl.canonical SeedRankOne.endpoint)
      (AffinePermutation.longest 5) + _ + _ + _ at h
  rw [SeedRankOne.canonical_source T W] at h
  exact add_right_cancel (add_right_cancel (add_right_cancel (add_right_cancel
    (h.symm.trans source_arithmetic))))

/-- The actual ordinary affine KL polynomial, not a supplied numerical
calibration or an additional hypothesis. -/
theorem diagonal_polynomial :
    T.kl.polynomial (AffinePermutation.longest 5)
      (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2)) =
      1 + 4*X + 5*X^2 + 4*X^3 + 2*X^4 := by
  rw [← suppliedSeedPolynomial_display]
  apply FamilyPolynomialReadout.of_source_coordinate
    (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2)
  change _ = normalize 9 suppliedSeedPolynomial
  rw [suppliedSeed_full]
  exact diagonal_source T W

theorem diagonal_mu :
    Hecke.familyMu (by decide : 2 ≤ 2) (by decide : 1 ≤ 2)
      (by decide : 2 ≤ 2) T.kl = 2 := by
  change (T.kl.polynomial (AffinePermutation.longest 5)
    (Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 2)
      (by decide : 2 ≤ 2))).coeff 4 = 2
  rw [diagonal_polynomial T W]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_one,
    Polynomial.coeff_X, Finset.Nat.antidiagonal_succ]

end Guralnick.SeedPolynomials
