import Guralnick.PolynomialWebLiterature
import Guralnick.ParabolicCosetFactorization
import Guralnick.KLInversion

/-!
# Standard expansions of the rank-one seed's spherical cosets

These are finite sums in the actual Hecke algebra. Their coefficients are
computed from the ordinary standard basis and the proved finite symmetrizer
formula. In particular the leading coefficient and strict positive-degree
bounds are not assumptions about the seed.
-/
noncomputable section
namespace Guralnick.SeedRankOneCosets
open Hecke ParabolicWeb Positivity CanonicalCorrection
open scoped BigOperators Classical
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
variable (I : Index n) (D : LongestData c I)

/-- The standard sum of a right spherical coset with left representative `x`. -/
def coset (x : AffinePermutation n) : Hecke.Algebra n :=
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  ∑ u : subgroup c I,
    (LaurentPolynomial.T ((c.system.length D.longest.val : ℤ) - c.system.length u.val) : R) •
      K.standard (x * u.val)

theorem coordinate (x y : AffinePermutation n) :
    letI : Finite (subgroup c I) := D.finite
    letI := Fintype.ofFinite (subgroup c I)
    K.standard.repr (coset K I D x) y =
      ∑ u : subgroup c I,
      if x * u.val = y then
        LaurentPolynomial.T ((c.system.length D.longest.val : ℤ) - c.system.length u.val)
      else 0 := by
  classical
  simp only [coset, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, K.standard.repr_self_apply]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp_all

theorem diagonal (x : AffinePermutation n) :
    K.standard.repr (coset K I D x) (x * D.longest.val) = 1 := by
  classical
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  rw [coordinate K I D]
  rw [Finset.sum_eq_single D.longest]
  · simp
  · intro u _ hu
    have h : x * u.val ≠ x * D.longest.val := by
      intro he
      exact hu (Subtype.ext (mul_left_cancel he))
    simp [h]
  · simp

theorem lower_zero (x y : AffinePermutation n) :
    LowerBound (K.standard.repr (coset K I D x) y) 0 := by
  classical
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  rw [coordinate K I D]
  apply lowerBound_sum
  intro u _
  split_ifs
  · exact lowerBound_mono (CanonicalRefinement.monomial_lowerBound _) (by
      have h := D.length_max u
      omega)
  · intro a _
    rfl

theorem lower_proper (x y : AffinePermutation n) (hy : y ≠ x * D.longest.val) :
    LowerBound (K.standard.repr (coset K I D x) y) 1 := by
  classical
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  rw [coordinate K I D]
  apply lowerBound_sum
  intro u _
  split_ifs with h
  · have hu : u.val ≠ D.longest.val := by
      intro he
      apply hy
      rw [←h, he]
    exact lowerBound_mono (CanonicalRefinement.monomial_lowerBound _) (by
      have h := ElementaryCoxeterLongest.length_lt_longest c I D u hu
      omega)
  · intro a _
    rfl

theorem coordinate_zero_of_length (x y : AffinePermutation n)
    (hx : ∀ s ∈ I.val, ¬c.system.IsRightDescent x s)
    (hy : c.system.length x + c.system.length D.longest.val < c.system.length y) :
    K.standard.repr (coset K I D x) y = 0 := by
  classical
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  rw [coordinate K I D]
  apply Finset.sum_eq_zero
  intro u _
  apply if_neg
  intro he
  have hl := ParabolicCosetFactorization.length_mul_right_of_no_descents c I x hx u
  have hm := D.length_max u
  rw [he] at hl
  omega

theorem source_zero (x : AffinePermutation n)
    (hx : ∀ s ∈ I.val, ¬c.system.IsRightDescent x s) (hne : x ≠ 1) :
    K.standard.repr (coset K I D x) D.longest.val = 0 := by
  classical
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  rw [coordinate K I D]
  apply Finset.sum_eq_zero
  intro u _
  apply if_neg
  intro he
  have hm : x ∈ subgroup c I := by
    have he' : x = D.longest.val * u.val⁻¹ := by rw [←he]; simp
    rw [he']
    exact (subgroup c I).mul_mem D.longest.property ((subgroup c I).inv_mem u.property)
  exact hne (ParabolicCosetFactorization.eq_one_of_no_right_descents c I ⟨x,hm⟩ hx)

/-- A standard word acting without descents realizes precisely this coset sum. -/
theorem word_mul (Ds : ∀ J : Index n, LongestData c J) (L : Laws K Ds)
    (x : AffinePermutation n) (l : List (Fin n))
    (h : ∀ u : subgroup c I, Hecke.word l * K.standard u.val = K.standard (x*u.val)) :
    Hecke.word l * symmetrizer K Ds I = coset K I (Ds I) x := by
  classical
  letI : Finite (subgroup c I) := (Ds I).finite
  letI := Fintype.ofFinite (subgroup c I)
  rw [L.standard_sum]
  simp only [coset, Finset.mul_sum, mul_smul_comm, h]

end Guralnick.SeedRankOneCosets
