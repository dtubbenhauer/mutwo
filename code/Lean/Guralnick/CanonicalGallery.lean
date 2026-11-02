import Guralnick.GaussianBasic
import Guralnick.Normalization
import Guralnick.Positivity
import Guralnick.DegreeBounds

/-!
# Degree support of the actual four-case gallery polynomial

The Gaussian polynomials are defined by q-Pascal recursion in `GaussianBasic`.
This file uses signed upper bounds on coefficient support, so empty factors
and negative lower indices are handled correctly. No polynomial degree
formula is postulated as a hypothesis.

The remaining geometric/combinatorial input in an application is that the
normalized polynomial here is the standard coordinate of the actual six-map
web. That count-to-Hecke identity is not assumed to follow from this file.
-/

noncomputable section

namespace Guralnick.CanonicalGallery

open scoped BigOperators
open Polynomial Positivity

def CoeffBound (p : ℤ[X]) (d : ℤ) : Prop :=
  ∀ k : ℕ, d < (k : ℤ) → p.coeff k = 0

theorem bound_zero (d : ℤ) : CoeffBound 0 d := by intro k _; simp

theorem bound_mono {p : ℤ[X]} {a b : ℤ} (h : CoeffBound p a) (hab : a ≤ b) :
    CoeffBound p b := by intro k hk; exact h k (lt_of_le_of_lt hab hk)

theorem bound_add {p q : ℤ[X]} {d : ℤ} (hp : CoeffBound p d) (hq : CoeffBound q d) :
    CoeffBound (p + q) d := by intro k hk; simp [hp k hk, hq k hk]

theorem bound_sub {p q : ℤ[X]} {d : ℤ} (hp : CoeffBound p d) (hq : CoeffBound q d) :
    CoeffBound (p - q) d := by intro k hk; simp [hp k hk, hq k hk]

theorem bound_mul {p q : ℤ[X]} {a b : ℤ} (hp : CoeffBound p a) (hq : CoeffBound q b) :
    CoeffBound (p * q) (a + b) := by
  intro k hk
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  by_cases hi : a < (ij.1 : ℤ)
  · rw [hp ij.1 hi, zero_mul]
  · have hj : b < (ij.2 : ℤ) := by omega
    rw [hq ij.2 hj, mul_zero]

/-- Signed quantum integer; negative and zero dimensions give zero. -/
def qInt (n : ℤ) : ℤ[X] := Gaussian.qInteger n.toNat

theorem qInt_coeff (n : ℤ) (k : ℕ) :
    (qInt n).coeff k = if (k : ℤ) < n then 1 else 0 := by
  unfold qInt
  rw [Gaussian.qInteger_coeff]
  split_ifs <;> omega

theorem qInt_bound (n : ℤ) : CoeffBound (qInt n) (n - 1) := by
  intro k hk
  rw [qInt_coeff, if_neg (by omega)]

@[simp] theorem qInt_zero : qInt 0 = 0 := by
  apply Polynomial.ext
  intro k
  simp [qInt_coeff]

@[simp] theorem qInt_nat (n : ℕ) : qInt (n : ℤ) = Gaussian.qInteger n := by
  simp [qInt]

@[simp] theorem qInt_one : qInt 1 = 1 := by
  simp [qInt, Gaussian.qInteger, Finset.sum_range_succ]

theorem qInt_difference_bound (n k : ℤ) (hk : k ≤ n) :
    CoeffBound (qInt n - qInt k) (n - 1) :=
  bound_sub (qInt_bound n) (bound_mono (qInt_bound k) (by omega))

/-- Gaussian polynomial with genuinely signed indices. In particular its
value at lower index `-1` is zero. -/
def qGauss (n k : ℤ) : ℤ[X] :=
  if 0 ≤ k ∧ k ≤ n then Gaussian.qBinomial n.toNat k.toNat else 0

theorem qGauss_nat {n k : ℕ} (hk : k ≤ n) :
    qGauss (n : ℤ) (k : ℤ) = Gaussian.qBinomial n k := by
  simp [qGauss, show (k : ℤ) ≤ n by exact_mod_cast hk]

theorem qGauss_bound (n k : ℤ) : CoeffBound (qGauss n k) (k * (n - k)) := by
  unfold qGauss
  split_ifs with hk
  · have hn : 0 ≤ n := by omega
    have hkn : k.toNat ≤ n.toNat := by omega
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    rw [Gaussian.qBinomial_natDegree hkn]
    have hcast : ((k.toNat * (n.toNat - k.toNat) : ℕ) : ℤ) = k * (n - k) := by
      rw [Nat.cast_mul, Nat.cast_sub hkn, Int.toNat_of_nonneg hk.1, Int.toNat_of_nonneg hn]
    omega
  · exact bound_zero _

/-- Converting a genuine polynomial degree bound into a lower Laurent
support bound under the paper's `v^D P(v^-2)` normalization. -/
theorem normalized_lowerBound (D d : ℤ) (p : ℤ[X]) (hp : CoeffBound p d) :
    LowerBound (normalize D p) (D - 2 * d) := by
  classical
  intro k hk
  by_contra hne
  have hmem : k ∈ (normalize D p).support := Finsupp.mem_support_iff.mpr hne
  have himage := Finsupp.mapDomain_support hmem
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp himage
  have hiz : p.coeff i ≠ 0 := Finsupp.mem_support_iff.mp hi
  exact hiz (hp i (by omega))

theorem normalized_coefficient (D : ℤ) (p : ℤ[X]) (k : ℕ) :
    normalize D p (D - 2 * (k : ℤ)) = p.coeff k :=
  Finsupp.mapDomain_apply (normalization_exponent_injective D) p.toFinsupp k

def baseDegree (l : ℤ) : ℤ := l^2 + 2*l - 3

def term0 (l a s β δ : ℤ) : ℤ[X] :=
  qInt l * (qInt (l+a+β) - qInt (s+δ-1)) * qInt a * qGauss (2*l) l
def term1 (l a s β δ : ℤ) : ℤ[X] :=
  qInt l * (qInt (l+a+β) - qInt (s+δ-1)) *
    (qInt (l+s) - qInt a) * qGauss (2*l-1) (l-1)
def term2 (l a s β δ : ℤ) : ℤ[X] :=
  qInt (l+1) * qInt (s+δ-1) * qInt a * qGauss (2*l+1) l
def term3 (l a s β δ : ℤ) : ℤ[X] :=
  qInt (l+1) * qInt (s+δ-1) * (qInt (l+s) - qInt a) * qGauss (2*l) (l-1)

/-- The four polynomial summands of equation (relevance-four-terms). -/
def count (l a s β δ : ℤ) : ℤ[X] :=
  term0 l a s β δ + term1 l a s β δ + term2 l a s β δ + term3 l a s β δ

def codimension (l a s β δ : ℤ) : ℤ :=
  s*(l+s) + a*(l+a-s+1) + β*(l+a+β) + (δ-β)*(s+δ-1)

def gap (l a s β δ : ℤ) : ℤ := 2*l*(l+1)-3+codimension l a s β δ

theorem term0_bound (l a s β δ : ℤ) (hH : s+δ-1 ≤ l+a+β) :
    CoeffBound (term0 l a s β δ) (baseDegree l + 2*a + β) := by
  have h := bound_mul (bound_mul (bound_mul (qInt_bound l)
    (qInt_difference_bound _ _ hH)) (qInt_bound a)) (qGauss_bound (2*l) l)
  convert h using 1 <;> try rfl
  unfold baseDegree
  ring

theorem term1_bound (l a s β δ : ℤ)
    (hH : s+δ-1 ≤ l+a+β) (hL : a ≤ l+s) :
    CoeffBound (term1 l a s β δ) (baseDegree l + a+s+β) := by
  have h := bound_mul (bound_mul (bound_mul (qInt_bound l)
    (qInt_difference_bound _ _ hH)) (qInt_difference_bound _ _ hL))
    (qGauss_bound (2*l-1) (l-1))
  convert h using 1 <;> try rfl
  unfold baseDegree
  ring

theorem term2_bound (l a s β δ : ℤ) :
    CoeffBound (term2 l a s β δ) (baseDegree l + a+s+δ) := by
  have h := bound_mul (bound_mul (bound_mul (qInt_bound (l+1))
    (qInt_bound (s+δ-1))) (qInt_bound a)) (qGauss_bound (2*l+1) l)
  convert h using 1 <;> try rfl
  unfold baseDegree
  ring

theorem term3_bound (l a s β δ : ℤ) (hL : a ≤ l+s) :
    CoeffBound (term3 l a s β δ) (baseDegree l + 2*s+δ-1) := by
  have h := bound_mul (bound_mul (bound_mul (qInt_bound (l+1))
    (qInt_bound (s+δ-1))) (qInt_difference_bound _ _ hL))
    (qGauss_bound (2*l) (l-1))
  convert h using 1 <;> try rfl
  unfold baseDegree
  ring

def degreeBound01 (l a s : ℤ) : ℤ :=
  baseDegree l + 2 * max a s + if a = s ∧ 1 ≤ a then 1 else 0

def degreeBound00 (l a s : ℤ) : ℤ :=
  baseDegree l + if s ≤ a then 2*a else 2*s-1

def degreeBound11 (l a s : ℤ) : ℤ :=
  baseDegree l + if s ≤ a then 2*a+1 else 2*s

theorem count_bound01 (l a s : ℤ) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hH : s ≤ l+a) (hL : a ≤ l+s) :
    CoeffBound (count l a s 0 1) (degreeBound01 l a s) := by
  have hmaxa := le_max_left a s
  have hmaxs := le_max_right a s
  have hc : 0 ≤ if a = s ∧ 1 ≤ a then (1 : ℤ) else 0 := by split_ifs <;> omega
  have hb0 := term0_bound l a s 0 1 (by omega)
  have hb1 := term1_bound l a s 0 1 (by omega) hL
  have hb3 := term3_bound l a s 0 1 hL
  unfold count
  apply bound_add (bound_add (bound_add
    (bound_mono hb0 (by unfold degreeBound01; omega))
    (bound_mono hb1 (by unfold degreeBound01; omega))) ?_)
    (bound_mono hb3 (by unfold degreeBound01; omega))
  by_cases ha0 : a = 0
  · simp only [ha0, term2, qInt_zero, mul_zero, zero_mul]
    exact bound_zero _
  · apply bound_mono (term2_bound l a s 0 1)
    unfold degreeBound01
    by_cases heq : a = s
    · rw [if_pos ⟨heq, by omega⟩]
      omega
    · rw [if_neg (fun h => heq h.1)]
      by_cases horder : a ≤ s
      · rw [max_eq_right horder]
        omega
      · rw [max_eq_left (by omega)]
        omega

theorem count_bound00 (l a s : ℤ)
    (hH : s-1 ≤ l+a) (hL : a ≤ l+s) :
    CoeffBound (count l a s 0 0) (degreeBound00 l a s) := by
  have hb0 := term0_bound l a s 0 0 (by omega)
  have hb1 := term1_bound l a s 0 0 (by omega) hL
  have hb2 := term2_bound l a s 0 0
  have hb3 := term3_bound l a s 0 0 hL
  unfold count
  apply bound_add (bound_add (bound_add
    (bound_mono hb0 ?_) (bound_mono hb1 ?_)) (bound_mono hb2 ?_)) (bound_mono hb3 ?_)
  all_goals unfold degreeBound00; split_ifs <;> omega

theorem count_bound11 (l a s : ℤ)
    (hH : s ≤ l+a+1) (hL : a ≤ l+s) :
    CoeffBound (count l a s 1 1) (degreeBound11 l a s) := by
  have hb0 := term0_bound l a s 1 1 (by omega)
  have hb1 := term1_bound l a s 1 1 (by omega) hL
  have hb2 := term2_bound l a s 1 1
  have hb3 := term3_bound l a s 1 1 hL
  unfold count
  apply bound_add (bound_add (bound_add
    (bound_mono hb0 ?_) (bound_mono hb1 ?_)) (bound_mono hb2 ?_)) (bound_mono hb3 ?_)
  all_goals unfold degreeBound11; split_ifs <;> omega

theorem allowance01 (l a s : ℤ) :
    2 * degreeBound01 l a s - gap l a s 0 1 =
      DegreeBounds.symmetricBound l (max a s) (min a s) := by
  unfold degreeBound01 gap codimension baseDegree DegreeBounds.symmetricBound
  by_cases horder : a ≤ s
  · rw [max_eq_right horder, min_eq_left horder]
    by_cases heq : a = s
    · subst s
      simp only [true_and]
      split_ifs <;> ring
    · have hne : s ≠ a := Ne.symm heq
      simp only [heq, hne, false_and, if_false]
      ring
  · rw [max_eq_left (by omega), min_eq_right (by omega)]
    have hne : a ≠ s := by omega
    simp only [hne, false_and, if_false]
    ring

theorem allowance00 (l a s : ℤ) :
    2 * degreeBound00 l a s - gap l a s 0 0 =
      if s ≤ a then DegreeBounds.bound00High l a s else DegreeBounds.bound00Low l a s := by
  unfold degreeBound00 gap codimension baseDegree DegreeBounds.bound00High DegreeBounds.bound00Low
  split_ifs <;> ring

theorem allowance11 (l a s : ℤ) :
    2 * degreeBound11 l a s - gap l a s 1 1 =
      if s ≤ a then DegreeBounds.bound11High l a s else DegreeBounds.bound11Low l a s := by
  unfold degreeBound11 gap codimension baseDegree DegreeBounds.bound11High DegreeBounds.bound11Low
  split_ifs <;> ring

/-- A nonzero bar-invariant canonical multiplicity forces nonnegative
degree allowance. This now uses the actual polynomial's proved support
bound and normalization, rather than assuming its numerical excess. -/
theorem allowance_nonnegative {d g rest : LP} {D B : ℤ} {p : ℤ[X]}
    (hd : d ≠ 0) (hpart : Nonnegative (d * g)) (hrest : Nonnegative rest)
    (hexp : d * normalize D p = d * g + rest)
    (hbar : BarSymmetric g) (hne : g ≠ 0) (hp : CoeffBound p B) :
    0 ≤ 2 * B - D := by
  by_contra h
  have hz := cleared_eq_zero_of_positive_bound hd hpart hrest hexp
    (normalized_lowerBound D B p hp) hbar (by omega)
  exact hne hz

/-- The six-position classification for the genuine four-case polynomial.
The previously separate degree-bound hypotheses have been discharged.
The only coefficient-identity input left is the count-to-canonical cleared
identity, which must come from the web evaluation and general KL positivity. -/
theorem six_positions_of_count (l a s β δ : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hrow : DegreeBounds.MiddleRow β δ) (hfeas : δ = 0 → 1 ≤ s)
    (hH : s+δ-1 ≤ l+a+β) (hL : a ≤ l+s)
    {d g rest : LP} (hd : d ≠ 0)
    (hpart : Nonnegative (d*g)) (hrest : Nonnegative rest)
    (hexp : d * normalize (gap l a s β δ) (count l a s β δ) = d*g+rest)
    (hbar : BarSymmetric g) (hne : g ≠ 0) :
    DegreeBounds.SixPositions β δ a s := by
  apply DegreeBounds.six_positions_of_bounds l a s 0 β δ hl ha hs (by omega) hrow hfeas
  · intro hβ hδ
    subst β
    subst δ
    rw [← allowance01]
    exact allowance_nonnegative hd hpart hrest hexp hbar hne
      (count_bound01 l a s ha hs (by omega) hL)
  · intro hβ hδ
    subst β
    subst δ
    rw [← allowance00]
    exact allowance_nonnegative hd hpart hrest hexp hbar hne
      (count_bound00 l a s (by omega) hL)
  · intro hβ hδ
    subst β
    subst δ
    rw [← allowance11]
    exact allowance_nonnegative hd hpart hrest hexp hbar hne
      (count_bound11 l a s (by omega) hL)

/-- At full rank the same signed-index four-case expression reduces to
the product stated separately in the manuscript. -/
theorem count_boundary (a s β δ : ℤ) :
    count 0 a s β δ = qInt a * qInt (s+δ-1) := by
  simp only [count, term0, term1, term2, term3, qInt_zero,
    zero_mul, add_zero, zero_add, zero_sub]
  norm_num [qGauss]
  ring

theorem boundary_count_bound (a s β δ : ℤ) :
    CoeffBound (count 0 a s β δ) (a+s+δ-3) := by
  rw [count_boundary]
  have h := bound_mul (qInt_bound a) (qInt_bound (s+δ-1))
  convert h using 1 <;> try rfl
  ring

/-- The full-rank boundary exclusion is also derived from the actual
polynomial, including zero factors and the middle-row feasibility. -/
theorem boundary_position_of_count (a s β δ : ℤ)
    (ha : 0 ≤ a) (hrow : DegreeBounds.MiddleRow β δ)
    (hfirst : a ≤ s) (hlast : s ≤ a+1-δ+β)
    {d g rest : LP} (hd : d ≠ 0)
    (hpart : Nonnegative (d*g)) (hrest : Nonnegative rest)
    (hexp : d * normalize (gap 0 a s β δ) (count 0 a s β δ) = d*g+rest)
    (hbar : BarSymmetric g) (hne : g ≠ 0) :
    β = 0 ∧ δ = 1 ∧ a = 1 ∧ s = 1 := by
  have ha1 : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    have hf : normalize (gap 0 a s β δ) (count 0 a s β δ) = 0 := by
      rw [ha0, count_boundary, qInt_zero, zero_mul]
      simp [normalize]
    exact hne (cleared_eq_zero_of_standard_zero hd hpart hrest hexp hf)
  have hb := allowance_nonnegative hd hpart hrest hexp hbar hne
    (boundary_count_bound a s β δ)
  apply DegreeBounds.boundary_position_of_bounds a s 0 β δ ha1 (by omega) hrow
  · intro hβ hδ
    subst β
    subst δ
    have hs : s = a := by omega
    refine ⟨hs, ?_⟩
    subst s
    unfold gap codimension at hb
    nlinarith
  · intro hβ hδ
    subst β
    subst δ
    have hs : s = a ∨ s = a+1 := by omega
    rcases hs with hs | hs
    · left
      refine ⟨hs, ?_⟩
      subst s
      unfold gap codimension at hb
      nlinarith
    · right
      refine ⟨hs, ?_⟩
      subst s
      unfold gap codimension at hb
      nlinarith
  · intro hβ hδ
    subst β
    subst δ
    have hs : s = a ∨ s = a+1 := by omega
    rcases hs with hs | hs
    · left
      refine ⟨hs, ?_⟩
      subst s
      unfold gap codimension at hb
      nlinarith
    · right
      refine ⟨hs, ?_⟩
      subst s
      unfold gap codimension at hb
      nlinarith

/-- The unique highest-degree type-F summand is an actual monic product. -/
theorem typeF_term2 (l : ℕ) :
    term2 l 1 1 0 1 = Gaussian.qInteger (l+1) * Gaussian.qBinomial (2*l+1) l := by
  have h1 : (l : ℤ)+1 = ((l+1 : ℕ) : ℤ) := by omega
  have h2 : 2*(l : ℤ)+1 = ((2*l+1 : ℕ) : ℤ) := by omega
  simp only [term2, h1, h2]
  norm_num only [show (1 : ℤ)+1-1 = 1 by omega, qInt_one, mul_one,
    qInt_nat, qGauss_nat (show l ≤ 2*l+1 by omega)]

theorem typeF_term2_top (l : ℕ) :
    (term2 l 1 1 0 1).coeff (l*l+2*l) = 1 := by
  rw [typeF_term2]
  have hi := Gaussian.qInteger_monic (l := l+1) (by omega)
  have hg := Gaussian.qBinomial_monic (n := 2*l+1) (k := l) (by omega)
  have hdeg : (Gaussian.qInteger (l+1) * Gaussian.qBinomial (2*l+1) l).natDegree =
      l*l+2*l := by
    rw [natDegree_mul hi.ne_zero hg.ne_zero,
      Gaussian.qInteger_natDegree (by omega), Gaussian.qBinomial_natDegree (by omega)]
    have hsub : 2*l+1-l = l+1 := by omega
    rw [hsub]
    simp only [Nat.add_sub_cancel]
    ring
  rw [← hdeg]
  exact (hi.mul hg).coeff_natDegree

theorem typeF_count_top (l : ℕ) (hl : 1 ≤ l) :
    (count l 1 1 0 1).coeff (l*l+2*l) = 1 := by
  have h0 := term0_bound (l : ℤ) 1 1 0 1 (by omega)
  have h1 := term1_bound (l : ℤ) 1 1 0 1 (by omega) (by omega)
  have h3 := term3_bound (l : ℤ) 1 1 0 1 (by omega)
  have hz0 := h0 (l*l+2*l) (by unfold baseDegree; push_cast; nlinarith)
  have hz1 := h1 (l*l+2*l) (by unfold baseDegree; push_cast; nlinarith)
  have hz3 := h3 (l*l+2*l) (by unfold baseDegree; push_cast; nlinarith)
  simp only [count, Polynomial.coeff_add, hz0, hz1, hz3, typeF_term2_top, add_zero, zero_add]

/-- The raw type-F standard coefficient has minimum degree zero and
constant coefficient one, including the full-rank endpoint `l=0`. -/
theorem typeF_standard (l : ℕ) :
    LowerBound (normalize (gap l 1 1 0 1) (count l 1 1 0 1)) 0 ∧
      normalize (gap l 1 1 0 1) (count l 1 1 0 1) 0 = 1 := by
  by_cases hl : l = 0
  · subst l
    norm_num only [Nat.cast_zero]
    have hpoly : count 0 1 1 0 1 = (1 : ℤ[X]) := by
      rw [count_boundary]
      norm_num
    have hgap : gap 0 1 1 0 1 = 0 := by norm_num [gap, codimension]
    rw [hpoly, hgap]
    constructor
    · have hp : CoeffBound (1 : ℤ[X]) 0 := by
        intro k hk
        simp [Polynomial.coeff_one, show k ≠ 0 by omega]
      simpa only [mul_zero, sub_zero] using normalized_lowerBound 0 0 1 hp
    · simpa using normalized_coefficient 0 (1 : ℤ[X]) 0
  · have hl1 : 1 ≤ l := by omega
    have hbound := count_bound01 (l : ℤ) 1 1 (by omega) (by omega) (by omega) (by omega)
    have hdegree : degreeBound01 l 1 1 = ((l*l+2*l : ℕ) : ℤ) := by
      norm_num [degreeBound01, baseDegree]
      ring
    have hgap : gap l 1 1 0 1 = 2*((l*l+2*l : ℕ) : ℤ) := by
      unfold gap codimension
      push_cast
      ring
    constructor
    · have h := normalized_lowerBound (gap l 1 1 0 1) _ _ hbound
      rw [hdegree, hgap] at h
      rw [hgap]
      simpa only [sub_self] using h
    · have h := normalized_coefficient (gap l 1 1 0 1) (count l 1 1 0 1) (l*l+2*l)
      rw [hgap, sub_self] at h
      rw [hgap, h, typeF_count_top l hl1]

/-- The type-F zero-or-one multiplicity conclusion, now with the raw
constant term and support derived from the actual count polynomial. -/
theorem typeF_zero_or_one (l : ℕ) {d g rest : LP}
    (hd : d ≠ 0) (hdpos : Nonnegative d)
    (hpart : Nonnegative (d*g)) (hrest : Nonnegative rest)
    (hexp : d * normalize (gap l 1 1 0 1) (count l 1 1 0 1) = d*g+rest)
    (hbar : BarSymmetric g) : g = 0 ∨ g = 1 :=
  cleared_zero_or_one hd hdpos hpart hrest hexp
    (typeF_standard l).1 (typeF_standard l).2 hbar

end Guralnick.CanonicalGallery
