import Guralnick.SeedRankOneCosets
import Guralnick.SeedCosets

/-!
# The seed rank-one correction in the actual affine Hecke algebra

The manuscript writes the inverse spherical module on the right as
`Mₑ b₀ b₄ b₁`. Here multiplication is on the left, so its actual Hecke
representative is `b₁ b₄ b₀ C_w₀`. Every statement uses this element and the
ordinary KL canonical basis; no seed polynomial is stipulated.
-/
noncomputable section
namespace Guralnick.SeedRankOne
open Hecke ParabolicWeb Positivity CanonicalCorrection
open scoped BigOperators

/-- The local bar-fixed Hecke map, with the manuscript's positive-degree convention. -/
def localMap {n : ℕ} (i : Fin n) : Hecke.Algebra n :=
  H i + algebraMap R (Hecke.Algebra n) (LaurentPolynomial.T 1)

theorem localMap_bar {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
    (i : Fin n) : K.bar (localMap i) = localMap i := by
  rw [localMap, map_add, K.bar_generator, K.bar_scalar]
  simp only [LaurentPolynomial.invert_T, map_sub]
  abel

def raw (T : Hecke.Theory 5) : Hecke.Algebra 5 :=
  localMap 1 * localMap 4 * localMap 0 * T.kl.canonical (AffinePermutation.longest 5)

def corrected (T : Hecke.Theory 5) : Hecke.Algebra 5 :=
  raw T - (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R) •
    T.kl.canonical (AffinePermutation.longest 5)

theorem raw_bar (T : Hecke.Theory 5) : T.kl.bar (raw T) = raw T := by
  simp only [raw, map_mul, localMap_bar, T.kl.bar_canonical]

theorem corrected_bar (T : Hecke.Theory 5) : T.kl.bar (corrected T) = corrected T := by
  unfold corrected
  rw [map_sub T.kl.bar (raw T)
    ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R) •
      T.kl.canonical (AffinePermutation.longest 5)), raw_bar, Hecke.bar_smul,
    map_add, LaurentPolynomial.invert_T, LaurentPolynomial.invert_T, T.kl.bar_canonical]
  congr 2
  simp [add_comm]

/-- The finite generators adjacent to the cut absorb into the spherical source. -/
theorem source_left_eigen (T : Hecke.Theory 5) (W : PolynomialWebLiterature T)
    (i : Fin 5) (hi : i ≠ 0) :
    H i * T.kl.canonical (AffinePermutation.longest 5) =
      (LaurentPolynomial.T (-1) : R) • T.kl.canonical (AffinePermutation.longest 5) := by
  have he := W.parabolic.left_eigen (CanonicalChains.source (by decide : 0<5)) i (by
    simpa [CanonicalChains.source, CanonicalChains.omitNode] using hi)
  simpa only [symmetrizer, W.finite_longest (by decide : 0<5)] using he

/-- Distributing the three local maps leaves four affine cosets and one source term. -/
theorem raw_expansion (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    raw T =
      H 1 * H 4 * H 0 * T.kl.canonical (AffinePermutation.longest 5) +
      (LaurentPolynomial.T 1 : R) •
        (H 1 * H 0 * T.kl.canonical (AffinePermutation.longest 5)) +
      (LaurentPolynomial.T 1 : R) •
        (H 4 * H 0 * T.kl.canonical (AffinePermutation.longest 5)) +
      (LaurentPolynomial.T 2 : R) •
        (H 0 * T.kl.canonical (AffinePermutation.longest 5)) +
      (LaurentPolynomial.T 3 + LaurentPolynomial.T 1 + LaurentPolynomial.T 1 +
        LaurentPolynomial.T (-1) : R) • T.kl.canonical (AffinePermutation.longest 5) := by
  have h1 := source_left_eigen T W (1 : Fin 5) (by decide)
  have h4 := source_left_eigen T W (4 : Fin 5) (by decide)
  unfold raw localMap
  simp only [add_mul, mul_add, mul_assoc, ←Algebra.smul_def, mul_smul_comm,
    smul_mul_assoc, smul_smul, h1, h4]
  simp only [←LaurentPolynomial.T_add]
  norm_num
  simp only [add_smul]
  abel

/-- The correction eliminates the only nonpositive-degree spherical contribution. -/
theorem corrected_expansion (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    corrected T =
      H 1 * H 4 * H 0 * T.kl.canonical (AffinePermutation.longest 5) +
      (LaurentPolynomial.T 1 : R) •
        (H 1 * H 0 * T.kl.canonical (AffinePermutation.longest 5)) +
      (LaurentPolynomial.T 1 : R) •
        (H 4 * H 0 * T.kl.canonical (AffinePermutation.longest 5)) +
      (LaurentPolynomial.T 2 : R) •
        (H 0 * T.kl.canonical (AffinePermutation.longest 5)) +
      (LaurentPolynomial.T 3 + LaurentPolynomial.T 1 : R) •
        T.kl.canonical (AffinePermutation.longest 5) := by
  rw [corrected, raw_expansion T W]
  simp only [add_smul]
  abel

/-- The actual standard spherical vector for each of the five cosets. -/
def spherical (T : Hecke.Theory 5) (k : Fin 5) : Hecke.Algebra 5 :=
  SeedRankOneCosets.coset T.kl (Family.source 2)
    (polynomialLongest T (Family.source 2)) (SeedCosets.coset k)

def cosetWord : Fin 5 → List (Fin 5) := ![[], [0], [1,0], [4,0], [1,4,0]]

theorem cosetWord_product (c : WindowCoxeter 5) (k : Fin 5) :
    c.system.wordProd (cosetWord k) = SeedCosets.coset k := by
  fin_cases k
  · simpa [cosetWord] using SeedCosets.coset_zero.symm
  · exact SeedCosets.word_zero c
  · exact SeedCosets.word_one_zero c
  · exact SeedCosets.word_four_zero c
  · exact SeedCosets.word_one_four_zero c

theorem cosetWord_reduced (c : WindowCoxeter 5) (k : Fin 5) :
    c.system.IsReduced (cosetWord k) := by
  change c.system.length (c.system.wordProd (cosetWord k)) = (cosetWord k).length
  rw [cosetWord_product, SeedCosets.length_coset]
  fin_cases k <;> rfl

theorem coset_standard_word (T : Hecke.Theory 5) (k : Fin 5) :
    T.kl.standard (SeedCosets.coset k) = Hecke.word (cosetWord k) := by
  rw [←cosetWord_product T.coxeter k]
  exact T.kl.standard_reduced _ (cosetWord_reduced T.coxeter k)

theorem word_spherical (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) (k : Fin 5) :
    Hecke.word (cosetWord k) * T.kl.canonical (AffinePermutation.longest 5) =
      spherical T k := by
  have he : symmetrizer T.kl W.longest (Family.source 2) =
      T.kl.canonical (AffinePermutation.longest 5) := by
    unfold symmetrizer
    rw [SeedCosets.source_longest]
  rw [←he]
  apply SeedRankOneCosets.word_mul T.kl (Family.source 2) W.longest W.parabolic
  intro u
  rw [←coset_standard_word]
  apply ParabolicIdealInclusion.standard_mul_of_length
  rw [SeedCosets.length_mul, SeedCosets.length_coset]

/-- The source is the identity coset of the finite symmetrizer. -/
theorem spherical_zero (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    spherical T 0 = T.kl.canonical (AffinePermutation.longest 5) := by
  have h := word_spherical T W 0
  simpa [cosetWord, Hecke.word] using h.symm

theorem corrected_spherical_expansion (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    corrected T = spherical T 4 +
      (LaurentPolynomial.T 1 : R) • spherical T 2 +
      (LaurentPolynomial.T 1 : R) • spherical T 3 +
      (LaurentPolynomial.T 2 : R) • spherical T 1 +
      (LaurentPolynomial.T 3 + LaurentPolynomial.T 1 : R) • spherical T 0 := by
  rw [corrected_expansion T W]
  have h1 := word_spherical T W 1
  have h2 := word_spherical T W 2
  have h3 := word_spherical T W 3
  have h4 := word_spherical T W 4
  simp [cosetWord, Hecke.word, ←mul_assoc] at h1 h2 h3 h4
  rw [h1, h2, h3, h4, spherical_zero T W]

/-- The rank-one upper endpoint is the actual family permutation. -/
abbrev endpoint : AffinePermutation 5 :=
  Guralnick.Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 1) (by decide : 1 ≤ 2)

theorem endpoint_eq : endpoint = SeedCosets.coset 4 * AffinePermutation.longest 5 := by
  rw [SeedCosets.affine_top]
  rfl

theorem endpoint_length (T : Hecke.Theory 5) : T.coxeter.system.length endpoint = 13 := by
  have h := SeedCosets.length_mul T.coxeter 4
    (polynomialLongest T (Family.source 2)).longest
  rw [SeedCosets.source_longest, SeedCosets.longest_length] at h
  simpa [endpoint_eq, SeedCosets.degree] using h

theorem spherical_diagonal (T : Hecke.Theory 5) :
    T.kl.standard.repr (spherical T 4) endpoint = 1 := by
  rw [endpoint_eq]
  have h := SeedRankOneCosets.diagonal T.kl (Family.source 2)
    (polynomialLongest T (Family.source 2)) (SeedCosets.coset 4)
  simpa only [spherical, SeedCosets.source_longest] using h

theorem spherical_top_zero (T : Hecke.Theory 5) (k : Fin 5) (hk : k ≠ 4) :
    T.kl.standard.repr (spherical T k) endpoint = 0 := by
  apply SeedRankOneCosets.coordinate_zero_of_length
  · exact SeedCosets.no_finite_descents T.coxeter k
  · rw [SeedCosets.length_coset, SeedCosets.source_longest,
      SeedCosets.longest_length, endpoint_length]
    fin_cases k <;> norm_num [SeedCosets.degree] at *
    exact hk rfl

theorem spherical_lower_zero (T : Hecke.Theory 5) (k : Fin 5) (y : AffinePermutation 5) :
    LowerBound (T.kl.standard.repr (spherical T k) y) 0 :=
  SeedRankOneCosets.lower_zero T.kl _ _ _ _

theorem spherical_lower_proper (T : Hecke.Theory 5) (y : AffinePermutation 5)
    (hy : y ≠ endpoint) :
    LowerBound (T.kl.standard.repr (spherical T 4) y) 1 := by
  apply SeedRankOneCosets.lower_proper
  simpa only [SeedCosets.source_longest, ←endpoint_eq] using hy

theorem corrected_diagonal (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    T.kl.standard.repr (corrected T) endpoint = 1 := by
  rw [corrected_spherical_expansion T W]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    spherical_diagonal, spherical_top_zero T 2 (by decide),
    spherical_top_zero T 3 (by decide), spherical_top_zero T 1 (by decide),
    spherical_top_zero T 0 (by decide), mul_zero, add_zero]

theorem corrected_lower (T : Hecke.Theory 5) (W : PolynomialWebLiterature T)
    (y : AffinePermutation 5) (hy : y ≠ endpoint) :
    LowerBound (T.kl.standard.repr (corrected T) y) 1 := by
  rw [corrected_spherical_expansion T W]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have shift (e : ℤ) (he : 1 ≤ e) (k : Fin 5) :
      LowerBound ((LaurentPolynomial.T e : R) * T.kl.standard.repr (spherical T k) y) 1 :=
    lowerBound_mono (lowerBound_mul (CanonicalRefinement.monomial_lowerBound e)
      (spherical_lower_zero T k y)) (by omega)
  apply lowerBound_add
  · exact lowerBound_add
      (lowerBound_add (lowerBound_add (spherical_lower_proper T y hy)
        (shift 1 (by omega) 2)) (shift 1 (by omega) 3)) (shift 2 (by omega) 1)
  · rw [add_mul]
    exact lowerBound_add (shift 3 (by omega) 0) (shift 1 (by omega) 0)

/-- The paper's rank-one correction is the ordinary KL canonical element,
proved from its full standard expansion, bar, and positive-degree bounds. -/
theorem canonical_identity (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    corrected T = T.kl.canonical endpoint := by
  apply sub_eq_zero.mp
  apply FidelityKL.bar_fixed_positive_zero T.kl
  · rw [map_sub, corrected_bar, T.kl.bar_canonical]
  · intro y
    rw [map_sub, Finsupp.sub_apply]
    by_cases hy : y = endpoint
    · subst y
      rw [corrected_diagonal T W, T.kl.canonical_diagonal, sub_self]
      intro a _
      rfl
    · exact lowerBound_sub (corrected_lower T W y hy) (T.kl.canonical_lower y endpoint hy)

theorem spherical_source_zero (T : Hecke.Theory 5) (k : Fin 5) (hk : k ≠ 0) :
    T.kl.standard.repr (spherical T k) (AffinePermutation.longest 5) = 0 := by
  have h := SeedRankOneCosets.source_zero T.kl (Family.source 2)
    (polynomialLongest T (Family.source 2)) (SeedCosets.coset k)
    (SeedCosets.no_finite_descents T.coxeter k)
  rw [SeedCosets.source_longest] at h
  apply h
  · intro he
    have hl := SeedCosets.length_coset T.coxeter k
    rw [he] at hl
    simp only [T.coxeter.system.length_one] at hl
    fin_cases k <;> simp [SeedCosets.degree] at *

/-- The actual fixed-`w₀` ordinary canonical coefficient is `v+v³`. -/
theorem canonical_source (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    T.kl.standard.repr (T.kl.canonical endpoint) (AffinePermutation.longest 5) =
      (LaurentPolynomial.T 1 + LaurentPolynomial.T 3 : R) := by
  rw [←canonical_identity T W, corrected_spherical_expansion T W]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    spherical_source_zero T 4 (by decide), spherical_source_zero T 2 (by decide),
    spherical_source_zero T 3 (by decide), spherical_source_zero T 1 (by decide),
    spherical_zero T W, T.kl.canonical_diagonal, mul_zero, add_zero, mul_one, add_comm]

/-- The complete source coordinate of the uncorrected rank-one web. -/
theorem raw_source (T : Hecke.Theory 5) (W : PolynomialWebLiterature T) :
    T.kl.standard.repr (raw T) (AffinePermutation.longest 5) =
      (LaurentPolynomial.T (-1) + 2 * LaurentPolynomial.T 1 + LaurentPolynomial.T 3 : R) := by
  have he : raw T = corrected T +
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R) •
        T.kl.canonical (AffinePermutation.longest 5) := by
    unfold corrected
    abel
  rw [he, canonical_identity T W]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    canonical_source T W, T.kl.canonical_diagonal, mul_one]
  ring

/-- The anti-involution reverses each local map, including its scalar branch. -/
theorem reverse_local_mul {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
    (i : Fin n) (x : Hecke.Algebra n) :
    HeckeInversion.reverseMap K (localMap i * x) =
      HeckeInversion.reverseMap K x * localMap i := by
  rw [localMap, add_mul, map_add, HeckeInversion.reverseMap_generator_mul,
    ←Algebra.smul_def, map_smul, mul_add]
  congr 1
  simpa only [Algebra.smul_def] using
    (Algebra.commutes (LaurentPolynomial.T 1 : R) (HeckeInversion.reverseMap K x))

/-- Literal conversion to the manuscript's inverse-permutation right-module word. -/
theorem raw_inverse_convention (T : Hecke.Theory 5) :
    HeckeInversion.reverseMap T.kl (raw T) =
      T.kl.canonical (AffinePermutation.longest 5) * localMap 0 * localMap 4 * localMap 1 := by
  unfold raw
  rw [mul_assoc, mul_assoc, reverse_local_mul, reverse_local_mul, reverse_local_mul,
    HeckeInversion.reverseMap_canonical, AffinePermutation.longest_inv]

end Guralnick.SeedRankOne
