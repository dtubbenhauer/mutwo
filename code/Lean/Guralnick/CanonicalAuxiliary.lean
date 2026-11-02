import Guralnick.CanonicalGallery
import Guralnick.CanonicalOneLine
import Guralnick.CanonicalCorrection

/-!
# Actual auxiliary count polynomials and their canonical degree tests

This file connects the one-line integer inequalities to the actual
q-Pascal polynomials. It proves strict positive Laurent support away from
the unique leading standard, and coefficient one at that standard.
It also proves the zero minimum and constant one of every full-spherical
Gaussian coordinate. The count-to-web identities are separate geometric
statements, not hypotheses about polynomial degrees.
-/

noncomputable section

namespace Guralnick.CanonicalAuxiliary

open Polynomial Positivity CanonicalGallery CanonicalCorrection

theorem normalize_add (D : ℤ) (p q : ℤ[X]) :
    normalize D (p+q) = normalize D p + normalize D q := by
  unfold normalize
  rw [Polynomial.toFinsupp_add, Finsupp.mapDomain_add]

/-- The two finite-gallery cases in the one-retained-line web. -/
def oneLineCount (n s d a b : ℤ) : ℤ[X] :=
  qInt a * qGauss n s + (qInt (d+b) - qInt a) * qGauss (n-1) (s-1)

theorem first_bound (n s a : ℤ) :
    CoeffBound (qInt a * qGauss n s) (CanonicalOneLine.firstDegree n s a) :=
  bound_mul (qInt_bound a) (qGauss_bound n s)

theorem second_bound (n s d a b : ℤ) (hab : a ≤ d+b) :
    CoeffBound ((qInt (d+b) - qInt a) * qGauss (n-1) (s-1))
      (CanonicalOneLine.secondDegree n s (d+b)) := by
  have h := bound_mul (qInt_difference_bound _ _ hab) (qGauss_bound (n-1) (s-1))
  convert h using 1 <;> try rfl
  unfold CanonicalOneLine.secondDegree
  ring

/-- Every proper one-line coordinate belongs to `v ℤ[v]`. Unlike the old
arithmetic lemma, this conclusion is about the actual normalized polynomial. -/
theorem oneLine_proper_positive (n s d a b : ℤ)
    (hn : 1 ≤ n) (hs : 0 ≤ s) (hsd : s ≤ d) (hnd : s ≤ n-d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ d+b) (hba : b ≤ n-d+a)
    (hne : ¬ (s = 0 ∧ a = 1 ∧ ((1 ≤ d ∧ b = 0) ∨ (d = 0 ∧ b = 1)))) :
    LowerBound (normalize (CanonicalOneLine.lengthGap n s d a b)
      (oneLineCount n s d a b)) 1 := by
  rw [oneLineCount, normalize_add]
  apply lowerBound_add
  · by_cases ha0 : a = 0
    · rw [ha0, qInt_zero, zero_mul]
      simp only [normalize, Polynomial.toFinsupp_zero, Finsupp.mapDomain_zero]
      intro k _
      rfl
    · have hdegree := CanonicalOneLine.first_strict_off_leading n s d a b hs
        (by omega) hnd (by omega) hb hab hne
      exact lowerBound_mono
        (normalized_lowerBound _ _ _ (first_bound n s a)) hdegree
  · have hdegree := CanonicalOneLine.second_negative n s d a b hn hs hsd hnd ha hb hba
    exact lowerBound_mono
      (normalized_lowerBound _ _ _ (second_bound n s d a b hab)) (by omega)

theorem oneLine_leading_count (n d b : ℤ) (hn : 1 ≤ n) :
    oneLineCount n 0 d 1 b = 1 := by
  simp [oneLineCount, qGauss, show (0 : ℤ) ≤ n by omega]

theorem oneLine_leading_gap (n d b : ℤ)
    (hpos : (1 ≤ d ∧ b = 0) ∨ (d = 0 ∧ b = 1)) :
    CanonicalOneLine.lengthGap n 0 d 1 b = 0 := by
  rcases hpos with ⟨_, hb⟩ | ⟨hd, hb⟩
  · subst b
    unfold CanonicalOneLine.lengthGap CanonicalOneLine.codimension
    ring
  · subst d
    subst b
    unfold CanonicalOneLine.lengthGap CanonicalOneLine.codimension
    ring

/-- The distinguished leading coefficient is the unit Laurent polynomial. -/
theorem oneLine_leading (n d b : ℤ) (hn : 1 ≤ n)
    (hpos : (1 ≤ d ∧ b = 0) ∨ (d = 0 ∧ b = 1)) :
    normalize (CanonicalOneLine.lengthGap n 0 d 1 b) (oneLineCount n 0 d 1 b) =
      (LaurentPolynomial.C 1 : LP) := by
  rw [oneLine_leading_gap n d b hpos, oneLine_leading_count n d b hn]
  change Finsupp.mapDomain (fun k : ℕ => (0 : ℤ)-2*k) (Finsupp.single 0 1) =
    Finsupp.single 0 1
  rw [Finsupp.mapDomain_single]
  norm_num

/-- The full-spherical Gaussian coordinate, with the half-gap written
as a natural number only after the valid `h<=n` range is specified. -/
def sphericalCoefficient (n h : ℕ) : LP :=
  normalize (2 * ((h*(n-h) : ℕ) : ℤ)) (Gaussian.qBinomial n h)

theorem spherical_standard (n h : ℕ) (hh : h ≤ n) :
    LowerBound (sphericalCoefficient n h) 0 ∧ sphericalCoefficient n h 0 = 1 := by
  have hp : CoeffBound (Gaussian.qBinomial n h) ((h*(n-h) : ℕ) : ℤ) := by
    intro k hk
    apply coeff_eq_zero_of_natDegree_lt
    rw [Gaussian.qBinomial_natDegree hh]
    omega
  constructor
  · have h := normalized_lowerBound (2*((h*(n-h) : ℕ) : ℤ)) _ _ hp
    simpa only [sub_self] using h
  · have he := normalized_coefficient (2*((h*(n-h) : ℕ) : ℤ))
      (Gaussian.qBinomial n h) (h*(n-h))
    have htop : (Gaussian.qBinomial n h).coeff (h*(n-h)) = 1 := by
      rw [← Gaussian.qBinomial_natDegree hh]
      exact (Gaussian.qBinomial_monic hh).coeff_natDegree
    rw [sub_self, htop] at he
    exact he

/-- At a full-spherical standard, the one-line coordinate has the exact
lower bound obtained from its actual two-case count (`a=b=0`). -/
theorem oneLine_full_spherical_lowerBound (n s d : ℤ) (hd : 0 ≤ d) :
    LowerBound (normalize (CanonicalOneLine.lengthGap n s d 0 0)
      (oneLineCount n s d 0 0)) (n-s-d+1) := by
  have hp := second_bound n s d 0 0 (by omega)
  have hn := normalized_lowerBound (CanonicalOneLine.lengthGap n s d 0 0) _ _ hp
  have he : CanonicalOneLine.lengthGap n s d 0 0 -
      2 * CanonicalOneLine.secondDegree n s (d+0) = n-s-d+1 := by
    unfold CanonicalOneLine.lengthGap CanonicalOneLine.codimension CanonicalOneLine.secondDegree
    ring
  rw [he] at hn
  simpa only [oneLineCount, qInt_zero, zero_mul, zero_add] using hn

/-- The strong-family contribution at any full-spherical coordinate starts
in degree three after its allowed negative multiplicity degree is included. -/
theorem strong_full_spherical_margin (m r s : ℤ) (hr : r ≤ m) {p : LP}
    (hp : LowerBound p (-(m-s-1))) :
    LowerBound (p * normalize
      (CanonicalOneLine.lengthGap (2*m+1-2*r) (s-r) (m-r) 0 0)
      (oneLineCount (2*m+1-2*r) (s-r) (m-r) 0 0)) 3 := by
  have hq := oneLine_full_spherical_lowerBound (2*m+1-2*r) (s-r) (m-r) (by omega)
  have he : -(m-s-1)+(2*m+1-2*r-(s-r)-(m-r)+1) = 3 := by ring
  simpa only [he] using lowerBound_mul hp hq

theorem weak_full_spherical_margin (m r s : ℤ) (hr : r ≤ m+1) {p : LP}
    (hp : LowerBound p (-(m-s-2))) :
    LowerBound (p * normalize
      (CanonicalOneLine.lengthGap (2*m+1-2*r) (s-r) (m+1-r) 0 0)
      (oneLineCount (2*m+1-2*r) (s-r) (m+1-r) 0 0)) 3 := by
  have hq := oneLine_full_spherical_lowerBound (2*m+1-2*r) (s-r) (m+1-r) (by omega)
  have he : -(m-s-2)+(2*m+1-2*r-(s-r)-(m+1-r)+1) = 3 := by ring
  simpa only [he] using lowerBound_mul hp hq

/-- The actual strong one-line polynomial at a desired family standard,
including the extra output-refinement power, has the stated lower bound. -/
theorem strong_at_typeF (k h : ℤ) (hh : 0 ≤ h) (hl : 1 ≤ k-h) :
    LowerBound (normalize (CanonicalOneLine.lengthGap (2*k+1) h k 1 1 + 1)
      (oneLineCount (2*k+1) h k 1 1)) ((k-h)+2*h+1) := by
  have hp : CoeffBound (oneLineCount (2*k+1) h k 1 1) (h*(2*k+1-h)) := by
    apply bound_add
    · simpa only [CanonicalOneLine.firstDegree, sub_self, zero_add] using first_bound (2*k+1) h 1
    · apply bound_mono (second_bound (2*k+1) h k 1 1 (by omega))
      have he := CanonicalOneLine.strong_piece_degree_difference k h
      unfold CanonicalOneLine.secondDegree
      nlinarith
  have hn := normalized_lowerBound (CanonicalOneLine.lengthGap (2*k+1) h k 1 1 + 1) _ _ hp
  rwa [CanonicalOneLine.strong_refined_minimum] at hn

theorem weak_at_typeF (k h : ℤ) (hh : 0 ≤ h) (hl : 1 ≤ k-h) :
    LowerBound (normalize (CanonicalOneLine.lengthGap (2*k+1) h (k+1) 1 1 + 1)
      (oneLineCount (2*k+1) h (k+1) 1 1)) ((k-h)+2*h+2) := by
  have hp : CoeffBound (oneLineCount (2*k+1) h (k+1) 1 1) (h*(2*k+1-h)) := by
    apply bound_add
    · simpa only [CanonicalOneLine.firstDegree, sub_self, zero_add] using first_bound (2*k+1) h 1
    · apply bound_mono (second_bound (2*k+1) h (k+1) 1 1 (by omega))
      have he := CanonicalOneLine.weak_piece_degree_difference k h
      unfold CanonicalOneLine.secondDegree
      nlinarith
  have hn := normalized_lowerBound (CanonicalOneLine.lengthGap (2*k+1) h (k+1) 1 1 + 1) _ _ hp
  rwa [CanonicalOneLine.weak_refined_minimum] at hn

end Guralnick.CanonicalAuxiliary
