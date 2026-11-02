import Guralnick.GaussianReciprocity
import Guralnick.Normalization
import Guralnick.CanonicalCorrection

/-!
# The Gaussian correction in the manuscript's Laurent convention

The normalization below uses the same actual `normalize` map as the KL
parameter-conversion file. It identifies `M_l` with the explicit bar-symmetric
correction and proves the positive support and critical coefficient of `Q_m`.
These are polynomial facts, not yet a statement that a web evaluates to Q.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.Gaussian

/-- The manuscript's `D_l=2l(l+1)-3`, as an integer. -/
def normalizationDegree (l : ℕ) : ℤ := 2*(l : ℤ)*(l+1)-3

theorem normalize_add (D : ℤ) (P Q : ℤ[X]) :
    normalize D (P+Q) = normalize D P + normalize D Q := by
  simp only [normalize, Polynomial.toFinsupp_add]
  exact Finsupp.mapDomain_add

theorem normalize_sub (D : ℤ) (P Q : ℤ[X]) :
    normalize D (P-Q) = normalize D P - normalize D Q := by
  simp only [normalize, Polynomial.toFinsupp_sub]
  exact map_sub (Finsupp.mapDomain.addMonoidHom _) _ _

theorem normalize_sum {ι : Type*} (s : Finset ι) (D : ℤ) (P : ι → ℤ[X]) :
    normalize D (∑ i ∈ s, P i) = ∑ i ∈ s, normalize D (P i) := by
  simp only [normalize, Polynomial.toFinsupp_sum]
  exact Finsupp.mapDomain_finset_sum

theorem normalize_monomial (D : ℤ) (n : ℕ) (a : ℤ) :
    normalize D (monomial n a) = Finsupp.single (D-2*n) a := by
  simp only [normalize, Polynomial.toFinsupp_monomial]
  exact Finsupp.mapDomain_single

/-- Normalization is multiplicative when the degree shifts add. -/
theorem normalize_mul (D E : ℤ) (P Q : ℤ[X]) :
    normalize (D+E) (P*Q) = normalize D P * normalize E Q := by
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ =>
    rw [add_mul, normalize_add, normalize_add, h₁, h₂, add_mul]
  | monomial n a =>
    induction Q using Polynomial.induction_on' with
    | add Q₁ Q₂ h₁ h₂ =>
      rw [mul_add, normalize_add, normalize_add, h₁, h₂, mul_add]
    | monomial r b =>
      rw [monomial_mul_monomial, normalize_monomial, normalize_monomial,
        normalize_monomial]
      rw [AddMonoidAlgebra.single_mul_single]
      congr 1
      push_cast
      ring

/-- Full identification of the explicit polynomial correction with `g_l`. -/
theorem normalize_M (l : ℕ) : normalize (normalizationDegree l) (M l) =
    CanonicalCorrection.correction l := by
  classical
  have he : M l = ∑ t ∈ Finset.range (l-1),
      (C (Nat.choose (t+3) 3 : ℤ)*X^(l*l+t) +
       C (Nat.choose (t+3) 3 : ℤ)*X^(l*l+(2*l-3-t))) := by
    unfold M H
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [pow_add]
    ring
  unfold normalize
  rw [he, Polynomial.toFinsupp_sum, Finsupp.mapDomain_finset_sum]
  unfold CanonicalCorrection.correction
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have hl : 3 ≤ 2*l := by omega
  have htdeg : t ≤ 2*l-3 := by omega
  simp only [Polynomial.toFinsupp_add, Polynomial.toFinsupp_C_mul_X_pow,
    mul_add,
    ← LaurentPolynomial.single_eq_C_mul_T]
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  have hfirst : normalizationDegree l - 2*((l*l+t : ℕ) : ℤ) =
      2*(l : ℤ)-3-2*t := by
    unfold normalizationDegree
    push_cast
    ring
  have hsecond : normalizationDegree l - 2*((l*l+(2*l-3-t) : ℕ) : ℤ) =
      -(2*(l : ℤ)-3-2*t) := by
    simp only [normalizationDegree, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub htdeg, Nat.cast_sub hl, Nat.cast_ofNat]
    ring
  rw [hfirst, hsecond]

theorem normalizationDegree_eq_critical {m : ℕ} (hm : 2 ≤ m) :
    normalizationDegree m = 2*(criticalDegree m : ℤ)+1 := by
  have h : 2 ≤ m*(m+1) := by nlinarith
  simp only [normalizationDegree, criticalDegree, Nat.cast_sub h,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- The entire corrected Gaussian polynomial has strictly positive Laurent
support. Its degree bound was proved above, not assumed as a support axiom. -/
theorem normalized_Q_lowerBound {m : ℕ} (hm : 2 ≤ m) :
    Positivity.LowerBound (normalize (normalizationDegree m) (Q m)) 1 := by
  classical
  intro k hk
  by_contra hne
  have hmem : k ∈ (normalize (normalizationDegree m) (Q m)).support :=
    Finsupp.mem_support_iff.mpr hne
  have himage := Finsupp.mapDomain_support hmem
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp himage
  have hiz : (Q m).coeff i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hd := (gaussian_cancellation hm).1
  have he := normalizationDegree_eq_critical hm
  have hlt : criticalDegree m < i := by
    change normalizationDegree m - 2*(i : ℤ) = k at hie
    omega
  exact hiz (coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hlt))

/-- The critical Laurent coefficient after the full explicit correction. -/
theorem normalized_Q_critical {m : ℕ} (hm : 2 ≤ m) :
    normalize (normalizationDegree m) (Q m) 1 = (Nat.choose (m+1) 2 : ℤ) := by
  rw [normalizationDegree_eq_critical hm, normalize_critical]
  exact (gaussian_cancellation hm).2

/-- Degree shift in a full-spherical standard coefficient. -/
def sphericalDegree (m r : ℕ) : ℤ := 2*(r : ℤ)*(2*m+1-r)

theorem normalizationDegree_split {m r : ℕ} (hr : r ≤ m) :
    normalizationDegree (m-r) + sphericalDegree m r = normalizationDegree m := by
  simp only [normalizationDegree, sphericalDegree, Nat.cast_sub hr]
  ring

/-- The exact residual appearing in the descending full-spherical
correction is normalization of the actual polynomial `Q_m`. -/
theorem full_spherical_residual (m : ℕ) :
    normalize (normalizationDegree m) (Y m) -
      (∑ r ∈ Finset.range (m-1), CanonicalCorrection.correction (m-r) *
        normalize (sphericalDegree m r) (difference (2*m+1) r)) =
      normalize (normalizationDegree m) (Q m) := by
  rw [Q, normalize_sub, normalize_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r ≤ m := by have := Finset.mem_range.mp hr; omega
  rw [← normalize_M, ← normalize_mul, normalizationDegree_split hr']

/-- The proposed correction's positive residual, with its exact standard
coefficient polynomials exposed, rather than supplied as a hypothesis. -/
theorem full_spherical_residual_lowerBound {m : ℕ} (hm : 2 ≤ m) :
    Positivity.LowerBound
      (normalize (normalizationDegree m) (Y m) -
        (∑ r ∈ Finset.range (m-1), CanonicalCorrection.correction (m-r) *
          normalize (sphericalDegree m r) (difference (2*m+1) r))) 1 := by
  rw [full_spherical_residual]
  exact normalized_Q_lowerBound hm

end Guralnick.Gaussian
