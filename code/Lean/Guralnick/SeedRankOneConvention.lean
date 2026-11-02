import Guralnick.SeedRankOne

/-!
# The seed word in the manuscript's inverse spherical convention

The operation here reverses Hecke words and sends each standard index to
its group inverse. It fixes the Laurent parameter; it is not the bar
involution. These identities identify the actual left-product seed with
the manuscript's `Mₑ b₀ b₄ b₁` and preserve the prescribed source coordinate.
-/

noncomputable section
namespace Guralnick.SeedRankOneConvention
open Hecke HeckeInversion SeedRankOne

/-- The same correction in the right spherical realization. -/
theorem corrected_inverse_word (T : Hecke.Theory 5) :
    reverseMap T.kl (corrected T) =
      T.kl.canonical (AffinePermutation.longest 5) * localMap 0 * localMap 4 * localMap 1 -
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R) •
        T.kl.canonical (AffinePermutation.longest 5) := by
  unfold corrected
  rw [map_sub (reverseMap T.kl) (raw T)
    ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R) •
      T.kl.canonical (AffinePermutation.longest 5))]
  rw [raw_inverse_convention, map_smul, reverseMap_canonical, AffinePermutation.longest_inv]

/-- The canonical correction stated with precisely the inverse upper index
and the rightward local word used in the paper. -/
theorem canonical_inverse_identity (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    T.kl.canonical endpoint⁻¹ =
      T.kl.canonical (AffinePermutation.longest 5) * localMap 0 * localMap 4 * localMap 1 -
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R) •
        T.kl.canonical (AffinePermutation.longest 5) := by
  rw [← reverseMap_canonical, ← canonical_identity T W]
  exact corrected_inverse_word T

/-- Inversion changes the upper index convention, while keeping `w₀`
and the entire normalized source polynomial unchanged. -/
theorem source_coordinate_preserved (T : Hecke.Theory 5) (x : Hecke.Algebra 5) :
    T.kl.standard.repr (reverseMap T.kl x) (AffinePermutation.longest 5) =
      T.kl.standard.repr x (AffinePermutation.longest 5) := by
  simpa only [AffinePermutation.longest_inv] using
    reverseMap_coordinate T.kl x (AffinePermutation.longest 5)

end Guralnick.SeedRankOneConvention
