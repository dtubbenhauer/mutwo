import Guralnick.Hecke
import Guralnick.KLDerivedBar
import Guralnick.KLInversion
import Guralnick.FamilyGap

/-!
# The fixed-source KL coefficients of the actual family

This module closes the window-to-length and parameter-normalization links.
Its external inputs are generic Coxeter/KL results only. In particular,
the family length gap is proved by the independent inversion calculation;
it is not an input to these theorems.
-/

noncomputable section
namespace Guralnick.Hecke

/-- General ordinary KL inversion invariance. The historical proposition
name is retained, but `Theory.inversion` now proves it from the KL basis. -/
def InversionInput {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c) : Prop :=
  ∀ y w, K.polynomial y⁻¹ w⁻¹ = K.polynomial y w

theorem family_length_gap {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2 * m + 1)) :
    (c.system.length (Family.upper hm hj hjm) : ℤ) -
      c.system.length (AffinePermutation.longest (2 * m + 1)) = gapFormula m j := by
  simp only [c.length_formula]
  exact Family.upper_inversion_gap hm hj hjm

/-- The family coefficient is now linked to the actual canonical coefficient
without a family-specific length or normalization hypothesis. -/
theorem familyMu_canonical {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    {c : WindowCoxeter (2 * m + 1)} (K : KLRealization c) :
    familyMu hm hj hjm K =
      (K.standard.repr (K.canonical (Family.upper hm hj hjm))
        (AffinePermutation.longest (2 * m + 1))) 1 :=
  familyMu_eq_canonical_coefficient hm hj hjm K (family_length_gap hm hj hjm c)

/-- The inverse upper label is exactly the one required by the trivial-induced
spherical convention: `w₀ * u⁻¹`. Ordinary source `w₀` is preserved. -/
theorem familyMu_inverse_canonical {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    {c : WindowCoxeter (2 * m + 1)} (K : KLRealization c) (hInv : InversionInput K) :
    familyMu hm hj hjm K =
      (K.standard.repr (K.canonical
        (AffinePermutation.longest (2 * m + 1) * (Family.affine hm hj hjm)⁻¹))
        (AffinePermutation.longest (2 * m + 1))) 1 := by
  rw [← Family.upper_inverse, K.polynomial_normalization, c.system.length_inv]
  have hp := hInv (AffinePermutation.longest (2 * m + 1)) (Family.upper hm hj hjm)
  simp only [AffinePermutation.longest_inv] at hp
  rw [hp, family_length_gap hm hj hjm c, normalize_family_critical _ hj hjm]
  rfl

/-- A collection of generic literature data at one rank. -/
structure Theory (n : ℕ) where
  coxeter : WindowCoxeter n
  kl : KLRealization coxeter
  positivity : PositivityInput kl

/-- Inversion is derived from the reduced-word basis and canonical
uniqueness, rather than supplied as a separate external theorem. -/
theorem Theory.inversion {n : ℕ} (T : Theory n) : InversionInput T.kl :=
  HeckeInversion.polynomial_inversion T.kl

abbrev TheoryFamily := ∀ (m : ℕ), 2 ≤ m → Theory (2 * m + 1)

/-- Natural-valued coefficients extracted from the actual ordinary KL
polynomials. Out-of-range inputs are zero; no in-range value is prescribed. -/
def coefficients (T : TheoryFamily) (m j : ℕ) : ℕ :=
  if hm : 2 ≤ m then
    if hj : 1 ≤ j then
      if hjm : j ≤ m then (familyMu hm hj hjm (T m hm).kl).toNat else 0
    else 0
  else 0

theorem coefficients_cast (T : TheoryFamily) {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (coefficients T m j : ℤ) = familyMu hm hj hjm (T m hm).kl := by
  simp only [coefficients, dif_pos hm, dif_pos hj, dif_pos hjm]
  exact Int.toNat_of_nonneg (familyMu_nonnegative hm hj hjm _ (T m hm).positivity)

theorem coefficients_canonical (T : TheoryFamily) {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (coefficients T m j : ℤ) =
      ((T m hm).kl.standard.repr ((T m hm).kl.canonical (Family.upper hm hj hjm))
        (AffinePermutation.longest (2 * m + 1))) 1 := by
  rw [coefficients_cast T hm hj hjm]
  exact familyMu_canonical hm hj hjm _

theorem coefficients_inverse_canonical (T : TheoryFamily) {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (coefficients T m j : ℤ) =
      ((T m hm).kl.standard.repr ((T m hm).kl.canonical
        (AffinePermutation.longest (2 * m + 1) * (Family.affine hm hj hjm)⁻¹))
        (AffinePermutation.longest (2 * m + 1))) 1 := by
  rw [coefficients_cast T hm hj hjm]
  exact familyMu_inverse_canonical hm hj hjm _ (T m hm).inversion

end Guralnick.Hecke
