import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Tactic

/-!
# Cleared-denominator positivity and Laurent support bounds

These are uniform statements about genuine `LaurentPolynomial ℤ` objects.
The application to canonical bases requires external hypotheses: the actual
coefficient identity, positivity after clearing the denominator, and bar
symmetry. This file does not assert the Hecke positivity theorem or that the
manuscript's web satisfies those hypotheses.

The denominator may be cancelled from *minimum degrees*. It must not be
cancelled from coefficientwise positivity. An explicit counterexample at the
end of this file proves that the latter inference is false.
-/

namespace Guralnick.Positivity

open scoped BigOperators

abbrev LP := LaurentPolynomial ℤ

@[simp] theorem coeff_add (p q : LP) (n : ℤ) : (p + q) n = p n + q n := rfl
@[simp] theorem coeff_sub (p q : LP) (n : ℤ) : (p - q) n = p n - q n := rfl
@[simp] theorem coeff_zero (n : ℤ) : (0 : LP) n = 0 := rfl

theorem coeff_C (a n : ℤ) : (LaurentPolynomial.C a : LP) n =
    if n = 0 then a else 0 := LaurentPolynomial.C_apply a n

def coeffHom (n : ℤ) : LP →+ ℤ where
  toFun p := p n
  map_zero' := rfl
  map_add' _ _ := rfl

def Nonnegative (p : LP) : Prop := ∀ n : ℤ, 0 ≤ p n
def CoeffLE (p q : LP) : Prop := ∀ n : ℤ, p n ≤ q n
def LowerBound (p : LP) (a : ℤ) : Prop := ∀ n : ℤ, n < a → p n = 0
def UpperBound (p : LP) (a : ℤ) : Prop := ∀ n : ℤ, a < n → p n = 0
def IsLowest (p : LP) (a : ℤ) : Prop := LowerBound p a ∧ p a ≠ 0
def BarSymmetric (p : LP) : Prop := LaurentPolynomial.invert p = p

theorem nonnegative_add {p q : LP} (hp : Nonnegative p) (hq : Nonnegative q) :
    Nonnegative (p + q) := by
  intro n
  exact add_nonneg (hp n) (hq n)

theorem nonnegative_mul {p q : LP} (hp : Nonnegative p) (hq : Nonnegative q) :
    Nonnegative (p * q) := by
  intro n
  rw [AddMonoidAlgebra.mul_apply]
  unfold Finsupp.sum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  dsimp
  split_ifs
  · exact mul_nonneg (hp i) (hq j)
  · exact le_rfl

theorem nonnegative_sum {ι : Type*} (s : Finset ι) (p : ι → LP)
    (hp : ∀ i ∈ s, Nonnegative (p i)) : Nonnegative (∑ i ∈ s, p i) := by
  intro n
  change 0 ≤ coeffHom n (∑ i ∈ s, p i)
  rw [map_sum]
  exact Finset.sum_nonneg (fun i hi => hp i hi n)

/-- A coefficientwise nonnegative remainder cannot cancel a contribution. -/
theorem component_le {whole part rest : LP}
    (hrest : Nonnegative rest) (h : whole = part + rest) : CoeffLE part whole := by
  intro n
  have he := congrArg (fun p : LP => p n) h
  change whole n = part n + rest n at he
  have hr := hrest n
  omega

theorem lowerBound_of_component {whole part : LP} {a : ℤ}
    (hpart : Nonnegative part) (hle : CoeffLE part whole)
    (hwhole : LowerBound whole a) : LowerBound part a := by
  intro n hn
  have hp := hpart n
  have hle' := hle n
  rw [hwhole n hn] at hle'
  omega

theorem lowerBound_of_positive_identity {whole part rest : LP} {a : ℤ}
    (hpart : Nonnegative part) (hrest : Nonnegative rest)
    (h : whole = part + rest) (hwhole : LowerBound whole a) :
    LowerBound part a :=
  lowerBound_of_component hpart (component_le hrest h) hwhole

theorem LowerBound.le_of_mem_support {p : LP} {a n : ℤ}
    (hp : LowerBound p a) (hn : n ∈ p.support) : a ≤ n := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hn) (hp n (by omega))

/-- A product has no exponents below the sum of lower support bounds;
coefficient signs are irrelevant. -/
theorem lowerBound_mul {p q : LP} {a b : ℤ}
    (hp : LowerBound p a) (hq : LowerBound q b) : LowerBound (p * q) (a + b) := by
  intro n hn
  rw [AddMonoidAlgebra.mul_apply]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hai := hp.le_of_mem_support hi
  have hbj := hq.le_of_mem_support hj
  have hne : i + j ≠ n := by omega
  simp [hne]

/-- The lowest product coefficient is a product of coefficients, even when
either factor has negative interior coefficients. -/
theorem coefficient_at_lowest {p q : LP} {a b : ℤ}
    (hp : LowerBound p a) (hq : LowerBound q b) :
    (p * q) (a + b) = p a * q b := by
  apply AddMonoidAlgebra.mul_apply_add_eq_mul_of_uniqueAdd
  intro i j hi hj hij
  have hai := hp.le_of_mem_support hi
  have hbj := hq.le_of_mem_support hj
  constructor <;> omega

theorem isLowest_mul {p q : LP} {a b : ℤ}
    (hp : IsLowest p a) (hq : IsLowest q b) : IsLowest (p * q) (a + b) := by
  refine ⟨lowerBound_mul hp.1 hq.1, ?_⟩
  rw [coefficient_at_lowest hp.1 hq.1]
  exact mul_ne_zero hp.2 hq.2

theorem exists_lowest {p : LP} (hp : p ≠ 0) : ∃ a, IsLowest p a := by
  classical
  have hs : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  refine ⟨p.support.min' hs, ?_, Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)⟩
  intro n hn
  by_contra hpn
  have hm := Finset.min'_le p.support n (Finsupp.mem_support_iff.mpr hpn)
  omega

/-- Cancellation of a nonzero factor from a lower support bound. The
factor's minimum exponent is supplied explicitly, avoiding a convention
for the valuation of zero. -/
theorem cancel_lowerBound {d g : LP} {a b : ℤ} (hd : IsLowest d a)
    (hprod : LowerBound (d * g) (a + b)) : LowerBound g b := by
  by_cases hg : g = 0
  · subst g
    intro n _
    rfl
  obtain ⟨c, hc⟩ := exists_lowest hg
  have hbc : b ≤ c := by
    by_contra h
    have hz := hprod (a + c) (by omega)
    exact (isLowest_mul hd hc).2 hz
  intro n hn
  exact hc.1 n (by omega)

/-- The manuscript's denominator-cancellation step, expressed as a support
bound. Positivity is assumed only for the *cleared* coefficient and the
remainder, never for `g` itself. -/
theorem cleared_lowerBound {d f g rest : LP} {b : ℤ}
    (hd : d ≠ 0) (hpart : Nonnegative (d * g)) (hrest : Nonnegative rest)
    (hidentity : d * f = d * g + rest) (hf : LowerBound f b) : LowerBound g b := by
  obtain ⟨a, ha⟩ := exists_lowest hd
  apply cancel_lowerBound ha
  exact lowerBound_of_positive_identity hpart hrest hidentity (lowerBound_mul ha.1 hf)

theorem bar_coeff {g : LP} (hg : BarSymmetric g) (n : ℤ) : g (-n) = g n := by
  have h := congrArg (fun p : LP => p n) hg
  simpa only [LaurentPolynomial.invert_apply] using h

theorem upperBound_of_bar {g : LP} {b : ℤ}
    (hg : BarSymmetric g) (hlow : LowerBound g b) : UpperBound g (-b) := by
  intro n hn
  rw [← bar_coeff hg n]
  exact hlow (-n) (by omega)

/-- Both support inequalities in the cleared-denominator lemma, with all
canonical-basis inputs left as explicit hypotheses. -/
theorem cleared_support_bounds {d f g rest : LP} {b : ℤ}
    (hd : d ≠ 0) (hpart : Nonnegative (d * g)) (hrest : Nonnegative rest)
    (hidentity : d * f = d * g + rest) (hf : LowerBound f b)
    (hg : BarSymmetric g) : LowerBound g b ∧ UpperBound g (-b) := by
  have hl := cleared_lowerBound hd hpart hrest hidentity hf
  exact ⟨hl, upperBound_of_bar hg hl⟩

theorem eq_zero_of_positive_bar_bound {g : LP} {b : ℤ}
    (hg : BarSymmetric g) (hlow : LowerBound g b) (hb : 0 < b) : g = 0 := by
  apply LaurentPolynomial.ext
  intro n
  by_cases hn : n < b
  · exact hlow n hn
  · exact upperBound_of_bar hg hlow n (by omega)

theorem constant_of_zero_bar_bound {g : LP}
    (hg : BarSymmetric g) (hlow : LowerBound g 0) :
    g = LaurentPolynomial.C (g 0) := by
  apply LaurentPolynomial.ext
  intro n
  by_cases hn : n = 0
  · subst n
    rw [coeff_C]
    rfl
  · have hz : g n = 0 := by
      by_cases hneg : n < 0
      · exact hlow n hneg
      · exact upperBound_of_bar hg hlow n (by omega)
    simp only [coeff_C, if_neg hn, hz]

theorem cleared_eq_zero_of_positive_bound {d f g rest : LP} {b : ℤ}
    (hd : d ≠ 0) (hpart : Nonnegative (d * g)) (hrest : Nonnegative rest)
    (hidentity : d * f = d * g + rest) (hf : LowerBound f b)
    (hg : BarSymmetric g) (hb : 0 < b) : g = 0 :=
  eq_zero_of_positive_bar_bound hg
    (cleared_lowerBound hd hpart hrest hidentity hf) hb

/-- If the standard coordinate is absent, its canonical coordinate is
absent too. This conclusion needs no bar symmetry. -/
theorem cleared_eq_zero_of_standard_zero {d f g rest : LP}
    (hd : d ≠ 0) (hpart : Nonnegative (d * g)) (hrest : Nonnegative rest)
    (hidentity : d * f = d * g + rest) (hf : f = 0) : g = 0 := by
  apply LaurentPolynomial.ext
  intro n
  have hlow : LowerBound f (n + 1) := by
    intro i _
    rw [hf]
    rfl
  exact cleared_lowerBound hd hpart hrest hidentity hlow n (by omega)

/-- A nonnegative nonzero denominator forces a *constant* quotient to be
nonnegative. This is the valid special case of positivity after division. -/
theorem constant_nonnegative {d g : LP} (hd : d ≠ 0) (hdpos : Nonnegative d)
    (hpart : Nonnegative (d * g)) (hc : g = LaurentPolynomial.C (g 0)) :
    0 ≤ g 0 := by
  obtain ⟨a, ha⟩ := exists_lowest hd
  have hda : 0 < d a := lt_of_le_of_ne (hdpos a) (Ne.symm ha.2)
  have hcoef : (d * LaurentPolynomial.C (g 0)) a = d a * g 0 := by
    exact AddMonoidAlgebra.mul_single_zero_apply d (g 0) a
  have hp := hpart a
  rw [hc, hcoef] at hp
  nlinarith

/-- The zero-bound conclusion of the manuscript's lemma. The stronger
claim that every `g` is coefficientwise nonnegative is not used. -/
theorem cleared_constant_of_zero_bound {d f g rest : LP}
    (hd : d ≠ 0) (hdpos : Nonnegative d)
    (hpart : Nonnegative (d * g)) (hrest : Nonnegative rest)
    (hidentity : d * f = d * g + rest) (hf : LowerBound f 0)
    (hg : BarSymmetric g) : g = LaurentPolynomial.C (g 0) ∧ 0 ≤ g 0 := by
  have hc := constant_of_zero_bar_bound hg
    (cleared_lowerBound hd hpart hrest hidentity hf)
  exact ⟨hc, constant_nonnegative hd hdpos hpart hc⟩

/-- Once `g` is constant and `f` has no negative exponents, comparison at
the denominator's lowest exponent gives the numerical multiplicity bound. -/
theorem constant_le_standard_constant {d f g rest : LP}
    (hd : d ≠ 0) (hdpos : Nonnegative d) (hrest : Nonnegative rest)
    (hidentity : d * f = d * g + rest) (hf : LowerBound f 0)
    (hc : g = LaurentPolynomial.C (g 0)) : g 0 ≤ f 0 := by
  obtain ⟨a, ha⟩ := exists_lowest hd
  have hda : 0 < d a := lt_of_le_of_ne (hdpos a) (Ne.symm ha.2)
  have hraw : (d * f) a = d a * f 0 := by
    simpa only [add_zero] using coefficient_at_lowest ha.1 hf
  have hpart : (d * g) a = d a * g 0 := by
    conv_lhs => rw [hc]
    exact AddMonoidAlgebra.mul_single_zero_apply d (g 0) a
  have hle := component_le hrest hidentity a
  rw [hraw, hpart] at hle
  nlinarith

/-- With raw constant coefficient one, the canonical multiplicity is zero
or one. Positivity of the entire Laurent quotient is not assumed. -/
theorem cleared_zero_or_one {d f g rest : LP}
    (hd : d ≠ 0) (hdpos : Nonnegative d)
    (hpart : Nonnegative (d * g)) (hrest : Nonnegative rest)
    (hidentity : d * f = d * g + rest) (hf : LowerBound f 0)
    (hf₀ : f 0 = 1) (hg : BarSymmetric g) :
    g = 0 ∨ g = 1 := by
  obtain ⟨hc, hnonneg⟩ :=
    cleared_constant_of_zero_bound hd hdpos hpart hrest hidentity hf hg
  have hle := constant_le_standard_constant hd hdpos hrest hidentity hf hc
  have hcases : g 0 = 0 ∨ g 0 = 1 := by omega
  rcases hcases with hzero | hone
  · left
    rw [hc, hzero, map_zero]
  · right
    rw [hc, hone, map_one]

/-! ## A positive product with a nonpositive quotient -/

noncomputable def counterDenominator : LP :=
  LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)

noncomputable def counterQuotient : LP :=
  LaurentPolynomial.T 2 - LaurentPolynomial.T 0 + LaurentPolynomial.T (-2)

theorem counterexample_product : counterDenominator * counterQuotient =
    LaurentPolynomial.T 3 + LaurentPolynomial.T (-3) := by
  simp only [counterDenominator, counterQuotient, add_mul, mul_add,
    mul_sub, ← LaurentPolynomial.T_add]
  norm_num
  abel

theorem counterexample_denominator_nonnegative : Nonnegative counterDenominator := by
  intro n
  simp only [counterDenominator, coeff_add, LaurentPolynomial.T_apply]
  split_ifs <;> omega

theorem counterexample_denominator_ne_zero : counterDenominator ≠ 0 := by
  intro hz
  have h₁ : counterDenominator 1 = 1 := by
    simp only [counterDenominator, coeff_add, LaurentPolynomial.T_apply]
    norm_num
  have h₀ := congrArg (fun p : LP => p 1) hz
  change counterDenominator 1 = 0 at h₀
  omega

theorem counterexample_product_nonnegative :
    Nonnegative (counterDenominator * counterQuotient) := by
  rw [counterexample_product]
  intro n
  simp only [coeff_add, LaurentPolynomial.T_apply]
  split_ifs <;> omega

theorem counterexample_negative_constant : counterQuotient 0 = -1 := by
  simp only [counterQuotient, coeff_add, coeff_sub, LaurentPolynomial.T_apply]
  norm_num

theorem counterexample_quotient_not_nonnegative : ¬ Nonnegative counterQuotient := by
  intro h
  have h₀ := h 0
  rw [counterexample_negative_constant] at h₀
  omega

theorem counterexample_denominator_bar : BarSymmetric counterDenominator := by
  unfold BarSymmetric counterDenominator
  simp [add_comm]

theorem counterexample_quotient_bar : BarSymmetric counterQuotient := by
  unfold BarSymmetric counterQuotient
  simp
  abel

/-- Even a nonzero positive bar-symmetric denominator and a bar-symmetric
quotient do not justify inferring quotient positivity from product positivity. -/
theorem positive_division_is_invalid :
    ∃ d g : LP, d ≠ 0 ∧ Nonnegative d ∧ BarSymmetric d ∧ BarSymmetric g ∧
      Nonnegative (d * g) ∧ ¬ Nonnegative g := by
  exact ⟨counterDenominator, counterQuotient,
    counterexample_denominator_ne_zero, counterexample_denominator_nonnegative,
    counterexample_denominator_bar, counterexample_quotient_bar,
    counterexample_product_nonnegative, counterexample_quotient_not_nonnegative⟩

end Guralnick.Positivity
