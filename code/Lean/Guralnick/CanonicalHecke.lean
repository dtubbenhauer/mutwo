import Guralnick.Hecke
import Guralnick.CanonicalBasis

/-!
# Canonical coordinates in the actual affine Hecke algebra

These lemmas instantiate the generic module-basis arguments in the presented
affine Hecke algebra. Bar symmetry of multiplicities is derived from the
specified bar and canonical basis; it is not an additional hypothesis about
the manuscript's coefficients.
-/

noncomputable section

namespace Guralnick.Hecke

open scoped BigOperators
open Positivity

variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

theorem bar_smul (r : R) (x : Algebra n) :
    K.bar (r • x) = LaurentPolynomial.invert r • K.bar x := by
  rw [Algebra.smul_def, map_mul, K.bar_scalar, Algebra.smul_def]

/-- The canonical coordinates of the bar are the inverted Laurent
coordinates. This follows from actual basis reconstruction and the fact
that each canonical basis vector is bar fixed. -/
theorem bar_canonical_coordinate (x : Algebra n) (w : AffinePermutation n) :
    K.canonical.repr (K.bar x) w = LaurentPolynomial.invert (K.canonical.repr x w) := by
  classical
  have hx : (∑ j ∈ (K.canonical.repr x).support,
      K.canonical.repr x j • K.canonical j) = x := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      K.canonical.linearCombination_repr x
  have h := congrArg (fun y => K.canonical.repr (K.bar y) w) hx
  simp only [map_sum, bar_smul K, K.bar_canonical, map_smul,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    K.canonical.repr_self_apply] at h
  rw [← h]
  rw [Finset.sum_eq_single w]
  · simp
  · intro j hj hjw
    simp [hjw]
  · intro hw
    rw [Finsupp.notMem_support_iff.mp hw]
    simp

theorem canonical_coordinate_barSymmetric {x : Algebra n}
    (hx : K.bar x = x) (w : AffinePermutation n) :
    BarSymmetric (K.canonical.repr x w) := by
  have h := bar_canonical_coordinate K x w
  rw [hx] at h
  exact h.symm

/-- Cancellation of a nonzero Laurent scalar in the Hecke algebra follows
from its actual basis. No unsupported division in an integral algebra is
performed. -/
theorem scalar_cancel (K : KLRealization c) {d : R} (hd : d ≠ 0) {x y : Algebra n}
    (h : d • x = d • y) : x = y := by
  apply K.canonical.repr.injective
  apply Finsupp.ext
  intro w
  have hc := congrArg (fun z : Algebra n => K.canonical.repr z w) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  exact mul_left_cancel₀ hd hc

/-- A bar-fixed cleared numerator and a bar-fixed nonzero denominator
force the integral quotient itself to be bar fixed. -/
theorem bar_of_cleared {d : R} (hd : d ≠ 0) (hdbar : BarSymmetric d)
    {x : Algebra n} (hx : K.bar (d • x) = d • x) : K.bar x = x := by
  rw [bar_smul K, hdbar] at hx
  exact scalar_cancel K hd hx

theorem canonical_coordinates_bar_of_cleared {d : R} (hd : d ≠ 0)
    (hdbar : BarSymmetric d) {x : Algebra n}
    (hx : K.bar (d • x) = d • x) (w : AffinePermutation n) :
    BarSymmetric (K.canonical.repr x w) :=
  canonical_coordinate_barSymmetric K (bar_of_cleared K hd hdbar hx) w

/-- Multiplication by a canonical basis vector, expanded through the actual
finite support of the first factor. -/
theorem canonical_mul_coordinate (x : Algebra n) (y z : AffinePermutation n) :
    K.canonical.repr (x * K.canonical y) z =
      ∑ w ∈ (K.canonical.repr x).support,
        K.canonical.repr x w * K.canonical.repr (K.canonical w * K.canonical y) z := by
  classical
  have hx : (∑ w ∈ (K.canonical.repr x).support,
      K.canonical.repr x w • K.canonical w) = x := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      K.canonical.linearCombination_repr x
  have h := congrArg (fun a : Algebra n => K.canonical.repr (a * K.canonical y) z) hx
  simpa only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] using h.symm

theorem nonnegative_mul_canonical (P : PositivityInput K) {x : Algebra n}
    (hx : ∀ w, Nonnegative (K.canonical.repr x w)) (y z : AffinePermutation n) :
    Nonnegative (K.canonical.repr (x * K.canonical y) z) := by
  rw [canonical_mul_coordinate K]
  apply nonnegative_sum
  intro w _
  exact nonnegative_mul (hx w) (P.product_nonnegative w y z)

/-- Positivity for arbitrary actual vectors with nonnegative canonical
coordinates, derived from the binary canonical structure constants. -/
theorem canonical_product_nonnegative (P : PositivityInput K) {x y : Algebra n}
    (hx : ∀ w, Nonnegative (K.canonical.repr x w))
    (hy : ∀ w, Nonnegative (K.canonical.repr y w)) (z : AffinePermutation n) :
    Nonnegative (K.canonical.repr (x*y) z) := by
  classical
  have hey : (∑ w ∈ (K.canonical.repr y).support,
      K.canonical.repr y w • K.canonical w) = y := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      K.canonical.linearCombination_repr y
  have h := congrArg (fun a : Algebra n => K.canonical.repr (x*a) z) hey
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  rw [← h]
  apply nonnegative_sum
  intro w hw
  exact nonnegative_mul (hy w) (nonnegative_mul_canonical K P hx w z)

/-- EW's two-factor positivity implies positivity of the actual threefold
product by its finite canonical expansion. -/
theorem canonical_product_three_nonnegative (P : PositivityInput K)
    (w x y z : AffinePermutation n) :
    Nonnegative (K.canonical.repr (K.canonical w * K.canonical x * K.canonical y) z) :=
  nonnegative_mul_canonical K P (P.product_nonnegative w x) y z

/-- The precise numerator positivity used by the six-map web. -/
theorem canonical_product_four_nonnegative (P : PositivityInput K)
    (w x y z t : AffinePermutation n) :
    Nonnegative (K.canonical.repr
      (K.canonical w * K.canonical x * K.canonical y * K.canonical z) t) :=
  nonnegative_mul_canonical K P (canonical_product_three_nonnegative K P w x y) z t

theorem cleared_coordinates_nonnegative (P : PositivityInput K)
    {d : R} {x : Algebra n} (w₁ w₂ w₃ w₄ : AffinePermutation n)
    (hx : d • x = K.canonical w₁ * K.canonical w₂ * K.canonical w₃ * K.canonical w₄)
    (t : AffinePermutation n) : Nonnegative (d * K.canonical.repr x t) := by
  have h := canonical_product_four_nonnegative K P w₁ w₂ w₃ w₄ t
  rw [← hx] at h
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h

/-- The coefficient identity used by the manuscript's positivity argument,
derived from the actual Hecke bases. The remainder is explicitly the finite
sum of all off-diagonal canonical contributions, and is proved nonnegative. -/
theorem positive_cleared_coordinate_identity (P : PositivityInput K)
    (d : R) (x : Algebra n)
    (hcleared : ∀ w, Nonnegative (d * K.canonical.repr x w))
    (w : AffinePermutation n) :
    ∃ rest : R, Nonnegative rest ∧
      d * K.standard.repr x w = d * K.canonical.repr x w + rest := by
  classical
  let S := insert w (K.canonical.repr x).support
  have hS : (K.canonical.repr x).support ⊆ S := Finset.subset_insert _ _
  have hw : w ∈ S := Finset.mem_insert_self _ _
  let rest := d * ∑ z ∈ S.erase w,
    K.canonical.repr x z * K.standard.repr (K.canonical z) w
  refine ⟨rest, ?_, ?_⟩
  · exact CanonicalBasis.cleared_remainder_nonnegative S d
      (fun i => K.canonical.repr x i) (fun i j => K.standard.repr (K.canonical j) i)
      w (fun i _ => hcleared i) (fun i _ => P.standard_nonnegative w i)
  · have hs := CanonicalBasis.split_expansion S (fun i => K.canonical.repr x i)
      (fun i j => K.standard.repr (K.canonical j) i) (fun i => K.standard.repr x i)
      w hw (K.canonical_diagonal w)
      (CanonicalBasis.coordinate_expansion_on K.standard K.canonical x S hS w)
    dsimp only at hs
    rw [hs, mul_add]

theorem canonical_lowerBound_of_standard (P : PositivityInput K)
    {d : R} (hd : d ≠ 0) (x : Algebra n)
    (hcleared : ∀ w, Nonnegative (d * K.canonical.repr x w))
    (w : AffinePermutation n) (a : ℤ)
    (hstandard : LowerBound (K.standard.repr x w) a) :
    LowerBound (K.canonical.repr x w) a := by
  obtain ⟨rest, hrest, hidentity⟩ := positive_cleared_coordinate_identity K P d x hcleared w
  exact cleared_lowerBound hd (hcleared w) hrest hidentity hstandard

theorem canonical_eq_zero_of_standard_zero (P : PositivityInput K)
    {d : R} (hd : d ≠ 0) (x : Algebra n)
    (hcleared : ∀ w, Nonnegative (d * K.canonical.repr x w))
    (w : AffinePermutation n) (hstandard : K.standard.repr x w = 0) :
    K.canonical.repr x w = 0 := by
  obtain ⟨rest, hrest, hidentity⟩ := positive_cleared_coordinate_identity K P d x hcleared w
  exact cleared_eq_zero_of_standard_zero hd (hcleared w) hrest hidentity hstandard

end Guralnick.Hecke
