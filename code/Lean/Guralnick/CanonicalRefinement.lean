import Guralnick.RefinementWindows
import Guralnick.FiniteSource
import Guralnick.GaussianNormalization

/-!
# Canonical coordinates under actual output refinement

The general Schur-basis input below says that a canonical element with
the specified descents lies in the span of normalized double-coset sums.
It is the general basis compatibility of Cui, not the canonicality of an
auxiliary web. From it we prove the normalization ratios for the actual
family windows, including the full-spherical factor v^(2(m-j)+3).
-/

noncomputable section
namespace Guralnick.CanonicalRefinement
open Hecke ParabolicWeb HeckeRefinement CanonicalSchur RefinementWindows Positivity Polynomial

variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I)

/-- General canonical/standard Schur-basis compatibility for every pair
of finitary parabolics. Williamson §2.3 gives this directly for arbitrary
finitary parabolics; Cui §2.5 and §3 give the affine Schur dictionary.
No conjugacy extension or particular web is assumed. -/
structure StandardCompatibility : Prop where
  canonical_span : ∀ (I J : Index n) (w : AffinePermutation n),
    letI : Finite (subgroup c I) := (D I).finite
    letI : Finite (subgroup c J) := (D J).finite
    DoubleMaximal c I J w →
      K.canonical w ∈ SchurCorner K (subgroup c I) (subgroup c J)

theorem canonical_coordinate_ratio (B : StandardCompatibility K D)
    (I J : Index n) (w y z : AffinePermutation n)
    (hw : DoubleMaximal c I J w)
    (hyz : Doset.mk (subgroup c I) (subgroup c J) y =
      Doset.mk (subgroup c I) (subgroup c J) z) :
    K.standard.repr (K.canonical w) y =
      (LaurentPolynomial.T ((c.system.length z : ℤ)-c.system.length y) : R) *
        K.standard.repr (K.canonical w) z := by
  letI := (D I).finite
  letI := (D J).finite
  exact corner_coordinate_ratio K (subgroup c I) (subgroup c J)
    (B.canonical_span I J w hw) y z hyz

theorem simple_same_coset (I J : Index n) (s : Fin n) (hs : s ∈ I.val)
    (w : AffinePermutation n) :
    Doset.mk (subgroup c I) (subgroup c J) w =
      Doset.mk (subgroup c I) (subgroup c J) (c.system.simple s*w) := by
  rw [Doset.eq]
  refine ⟨c.system.simple s, Subgroup.subset_closure ⟨s, hs, rfl⟩,
    1, (subgroup c J).one_mem, ?_⟩
  simp

theorem normalize_shift (e d : ℤ) (p : ℤ[X]) :
    (LaurentPolynomial.T e : LP) * normalize d p = normalize (e+d) p := by
  have h := Gaussian.normalize_mul e d (1 : ℤ[X]) p
  have he : normalize e (1 : ℤ[X]) = (LaurentPolynomial.T e : LP) := by
    rw [show (1 : ℤ[X]) = Polynomial.monomial 0 1 by simp,
      Gaussian.normalize_monomial]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    rfl
  simpa only [he, one_mul] using h.symm

theorem monomial_lowerBound (e : ℤ) : LowerBound (LaurentPolynomial.T e : LP) e := by
  intro a ha
  change (Finsupp.single e (1 : ℤ)) a = 0
  exact Finsupp.single_eq_of_ne (ne_of_gt ha)

theorem canonical_coordinate_lowerBound_zero (y w : AffinePermutation n) :
    LowerBound (K.standard.repr (K.canonical w) y) 0 := by
  by_cases h : y=w
  · subst y
    rw [K.canonical_diagonal]
    simpa only [LaurentPolynomial.T_zero] using monomial_lowerBound 0
  · intro a ha
    exact K.canonical_lower y w h a (by omega)

variable {m : ℕ} {c : WindowCoxeter (2*m+1)}

theorem spherical_same_coset {j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    Doset.mk (subgroup c (Family.source m)) (subgroup c (Family.source m))
      (Guralnick.Family.upper hm hj hjm) =
    Doset.mk (subgroup c (Family.source m)) (subgroup c (Family.source m))
      (CanonicalSpherical.index m j) := by
  rw [Doset.eq]
  let u := Guralnick.Family.upper hm hj hjm
  let v := CanonicalSpherical.index m j
  let σ := v.residue*u.residue⁻¹
  refine ⟨AffinePermutation.finiteEmbedding (2*m+1) σ,
    FiniteSource.finiteEmbedding_mem_source m c σ,
    1, (subgroup c (Family.source m)).one_mem, ?_⟩
  simpa only [mul_one] using (finite_left_of_winding_eq u v (spherical_winding hm hj hjm)).symm

/-- The full-spherical refinement factor at every actual family standard. -/
theorem spherical_at_family (K : KLRealization c)
    (D : ∀ I : Index (2*m+1), LongestData c I) (B : StandardCompatibility K D)
    {j s : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (hs : s ≤ m) :
    K.standard.repr (K.canonical (CanonicalSpherical.index m s))
        (Guralnick.Family.upper hm hj hjm) =
      (LaurentPolynomial.T (2*((m : ℤ)-j)+3) : R) *
        K.standard.repr (K.canonical (CanonicalSpherical.index m s))
          (CanonicalSpherical.index m j) := by
  rw [canonical_coordinate_ratio K D B (Family.source m) (Family.source m) _ _ _
    (CanonicalSpherical.index_doubleMaximal hs c) (spherical_same_coset hm hj hjm),
    spherical_length_shift hm hj hjm c]

/-- A one-line coarse canonical element acquires exactly one v at a
family standard. The source and the canonical Hecke element are unchanged. -/
theorem oneLine_at_family (K : KLRealization c)
    (D : ∀ I : Index (2*m+1), LongestData c I) (B : StandardCompatibility K D)
    {j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (I : Index (2*m+1)) (w : AffinePermutation (2*m+1))
    (hw : DoubleMaximal c I (Family.source m) w) (s : Fin (2*m+1))
    (hs : s ∈ I.val) (hwhich : s.val=m ∨ s.val=m+1) :
    K.standard.repr (K.canonical w) (Guralnick.Family.upper hm hj hjm) =
      (LaurentPolynomial.T 1 : R) *
        K.standard.repr (K.canonical w) (c.system.simple s*Guralnick.Family.upper hm hj hjm) := by
  have hlen : c.system.length (c.system.simple s*Guralnick.Family.upper hm hj hjm) =
      c.system.length (Guralnick.Family.upper hm hj hjm)+1 := by
    rcases hwhich with h|h
    · have he : s=⟨m, by omega⟩ := Fin.ext h
      rw [he]
      exact weak_length_shift hm hj hjm c
    · have he : s=⟨m+1, by omega⟩ := Fin.ext h
      rw [he]
      exact strong_length_shift hm hj hjm c
  rw [canonical_coordinate_ratio K D B I (Family.source m) _ _ _ hw
    (simple_same_coset I (Family.source m) s hs _), hlen]
  simp

/-- The proved refinement ratio converts a nonnegative minimum degree at
the coarse spherical standard to the exact refined lower bound. -/
theorem spherical_refined_lowerBound (K : KLRealization c)
    (D : ∀ I : Index (2*m+1), LongestData c I) (B : StandardCompatibility K D)
    {j s : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (hs : s ≤ m) :
    LowerBound (K.standard.repr (K.canonical (CanonicalSpherical.index m s))
      (Guralnick.Family.upper hm hj hjm)) (2*((m : ℤ)-j)+3) := by
  rw [spherical_at_family K D B hm hj hjm hs]
  simpa only [add_zero] using lowerBound_mul (monomial_lowerBound _)
    (canonical_coordinate_lowerBound_zero K _ _)

end Guralnick.CanonicalRefinement
