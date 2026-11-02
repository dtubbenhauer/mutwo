import Guralnick.AffineGroup
import Guralnick.AffineAdjacentInversions
import Guralnick.Normalization
import Guralnick.Positivity
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# An actual affine Hecke algebra and precise generic literature inputs

The algebra below is the quotient of the free Laurent-polynomial algebra
by the quadratic and braid relations. Thus the algebra, its generators and
word evaluations are defined before any basis data are supplied.

`WindowCoxeter` packages the general affine-permutation Coxeter theorem,
and length formula (Björner--Brenti, Affine
Permutations of Type A, Propositions 3.1--3.3). `KLRealization` packages
the general ordinary KL basis theorem for this algebra. The adjacent-entry
descent criterion is derived below from the actual inversion sum. These are explicit
arguments, never declared axioms, and contain no family-specific values,
row-sum identity, gallery count or cohomology conclusion.
-/

noncomputable section
namespace Guralnick.Hecke
open scoped BigOperators

abbrev R := LaurentPolynomial ℤ
abbrev Free (n : ℕ) := FreeAlgebra R (Fin n)

def alternating {n : ℕ} (i j : Fin n) (a : ℕ) : List (Fin n) :=
  (List.range a).map fun k => if k % 2 = 0 then i else j

def freeWord {n : ℕ} (l : List (Fin n)) : Free n :=
  (l.map (FreeAlgebra.ι R)).prod

/-- Exactly `(H_s-v⁻¹)(H_s+v)=0`, and the cyclic braid relations. -/
inductive Relation (n : ℕ) : Free n → Free n → Prop
  | quadratic (i : Fin n) : Relation n
      (FreeAlgebra.ι R i * FreeAlgebra.ι R i)
      (1 + algebraMap R (Free n) (LaurentPolynomial.T (-1) - LaurentPolynomial.T 1) *
        FreeAlgebra.ι R i)
  | braid (i j : Fin n) : Relation n
      (freeWord (alternating i j (AffineCoxeter.matrix n i j)))
      (freeWord (alternating j i (AffineCoxeter.matrix n i j)))

/-- The affine Hecke algebra as an algebra presented by generators and relations. -/
abbrev Algebra (n : ℕ) := RingQuot (Relation n)

def quotient (n : ℕ) : Free n →ₐ[R] Algebra n := RingQuot.mkAlgHom R (Relation n)

def H {n : ℕ} (i : Fin n) : Algebra n := quotient n (FreeAlgebra.ι R i)

def word {n : ℕ} (l : List (Fin n)) : Algebra n := (l.map H).prod

theorem quotient_freeWord {n : ℕ} (l : List (Fin n)) :
    quotient n (freeWord l) = word l := by
  simp only [freeWord, word, map_list_prod, List.map_map]
  rfl

theorem quadratic {n : ℕ} (i : Fin n) :
    H i * H i = 1 + algebraMap R (Algebra n)
      (LaurentPolynomial.T (-1) - LaurentPolynomial.T 1) * H i := by
  have h := RingQuot.mkAlgHom_rel R (Relation.quadratic (n := n) i)
  simpa only [map_mul, map_add, map_one, AlgHom.commutes] using h

theorem braid {n : ℕ} (i j : Fin n) :
    word (alternating i j (AffineCoxeter.matrix n i j)) =
      word (alternating j i (AffineCoxeter.matrix n i j)) := by
  have h := RingQuot.mkAlgHom_rel R (Relation.braid (n := n) i j)
  change quotient n _ = quotient n _ at h
  simpa only [quotient_freeWord] using h

/-- The known adjacent-transposition windows; generator zero crosses the seam. -/
def simpleEntry {n : ℕ} (s i : Fin n) : ℤ :=
  if s.val = 0 then
    if i.val = 0 then 0 else if i.val + 1 = n then (n : ℤ) + 1 else i.val + 1
  else if i.val + 1 = s.val then (s.val : ℤ) + 1
    else if i = s then s.val else i.val + 1

/-- General literature input for the actual affine-window group.
The intended range is `n ≥ 3`. No special family is mentioned. -/
structure WindowCoxeter (n : ℕ) where
  system : CoxeterSystem (AffineCoxeter.matrix n) (AffinePermutation n)
  simple_window : ∀ s i, (system.simple s).entry i = simpleEntry s i
  length_formula : ∀ w, system.length w = w.inversionCount

theorem WindowCoxeter.simple_finite {n : ℕ} (c : WindowCoxeter n)
    (a b : Fin n) (hab : a.val+1=b.val) :
    c.system.simple b = AffinePermutation.finiteEmbedding n (Equiv.swap a b) := by
  letI : NeZero n := ⟨Nat.ne_of_gt (Fin.pos a)⟩
  apply AffineAdjacentInversions.ext_entry
  funext i
  rw [c.simple_window]
  have hb : b.val≠0 := by omega
  have hne : a≠b := fun h => by have hv := congrArg Fin.val h; omega
  have he : i.val+1=b.val ↔ i=a := by
    constructor
    · intro h; exact Fin.ext (by omega)
    · intro h; rw [h]; exact hab
  simp only [simpleEntry,if_neg hb,he,AffinePermutation.entry,
    AffinePermutation.finiteEmbedding,Pi.zero_apply,mul_zero,add_zero]
  by_cases hi : i=a
  · subst i
    simp [hne]
  · by_cases hj : i=b
    · subst i
      simp only [if_neg hi,if_pos rfl,Equiv.swap_apply_right]
      simpa [AffinePermutation.finiteEmbedding] using
        (show (b.val : ℤ)=(a.val : ℤ)+1 by exact_mod_cast hab.symm)
    · simp [hi,hj,Equiv.swap_apply_of_ne_of_ne hi hj]

/-- The finite descent test is derived from the explicit affine inversion
sum; it is not a separate field of the Coxeter realization. -/
theorem WindowCoxeter.finite_descent {n : ℕ} (c : WindowCoxeter n)
    (w : AffinePermutation n) (a b : Fin n) (hab : a.val+1=b.val) :
    c.system.IsRightDescent w b ↔ w.entry b<w.entry a := by
  change c.system.length (w*c.system.simple b)<c.system.length w ↔ _
  rw [c.length_formula,c.length_formula,c.simple_finite a b hab]
  exact AffineAdjacentInversions.inversion_swap_lt_iff w a b hab

/-- Bruhat relation defined by subwords of a reduced expression. -/
def Bruhat {n : ℕ} (c : WindowCoxeter n) (y w : AffinePermutation n) : Prop :=
  ∃ a b : List (Fin n), a.Sublist b ∧ c.system.IsReduced b ∧
    c.system.wordProd a = y ∧ c.system.wordProd b = w

/-- Precisely stated general ordinary KL-basis data. The standard basis is
tied to reduced words in the presented algebra. Canonical basis elements
are tied to its bar and triangularity, and polynomial coefficients to the
usual parameter conversion. This interface supplies no original web lemma. -/
structure KLRealization {n : ℕ} (c : WindowCoxeter n) where
  standard : Basis (AffinePermutation n) R (Algebra n)
  standard_reduced : ∀ l : List (Fin n), c.system.IsReduced l →
    standard (c.system.wordProd l) = word l
  bar : Algebra n ≃+* Algebra n
  bar_scalar : ∀ r : R, bar (algebraMap R (Algebra n) r) =
    algebraMap R (Algebra n) (LaurentPolynomial.invert r)
  bar_generator : ∀ i : Fin n, bar (H i) = H i +
    algebraMap R (Algebra n) (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1))
  canonical : Basis (AffinePermutation n) R (Algebra n)
  bar_canonical : ∀ w, bar (canonical w) = canonical w
  canonical_diagonal : ∀ w, standard.repr (canonical w) w = 1
  canonical_lower : ∀ y w, y ≠ w →
    Positivity.LowerBound (standard.repr (canonical w) y) 1
  canonical_support : ∀ y w, standard.repr (canonical w) y ≠ 0 → Bruhat c y w
  polynomial : AffinePermutation n → AffinePermutation n → Polynomial ℤ
  polynomial_normalization : ∀ y w,
    standard.repr (canonical w) y =
      normalize ((c.system.length w : ℤ) - c.system.length y) (polynomial y w)

/-- Elias--Williamson Corollary 1.2, for the entire ordinary Coxeter basis.
These are generic positivity assumptions, not positivity of a quotient or
an assumption about the special web. -/
structure PositivityInput {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c) : Prop where
  standard_nonnegative : ∀ y w, Positivity.Nonnegative (K.standard.repr (K.canonical w) y)
  product_nonnegative : ∀ x y z,
    Positivity.Nonnegative (K.canonical.repr (K.canonical x * K.canonical y) z)

theorem polynomial_coeff_nonnegative {n : ℕ} {c : WindowCoxeter n}
    (K : KLRealization c) (P : PositivityInput K) (y w : AffinePermutation n) (a : ℕ) :
    0 ≤ (K.polynomial y w).coeff a := by
  let d : ℤ := (c.system.length w : ℤ) - c.system.length y
  have hp := P.standard_nonnegative y w (d - 2 * (a : ℤ))
  rw [K.polynomial_normalization] at hp
  have he := Finsupp.mapDomain_apply (normalization_exponent_injective d)
    (K.polynomial y w).toFinsupp a
  change normalize d (K.polynomial y w) (d - 2 * (a : ℤ)) =
    (K.polynomial y w).coeff a at he
  change 0 ≤ normalize d (K.polynomial y w) (d - 2 * (a : ℤ)) at hp
  rwa [he] at hp

/-- The actual ordinary fixed-source KL critical coefficient, dependent on
the generic basis theorem above. It is not defined to be `j` or a row sum. -/
def familyMu {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    {c : WindowCoxeter (2 * m + 1)} (K : KLRealization c) : ℤ :=
  (K.polynomial (AffinePermutation.longest (2 * m + 1))
    (Family.upper hm hj hjm)).coeff (criticalIndex m j)

theorem familyMu_nonnegative {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    {c : WindowCoxeter (2 * m + 1)} (K : KLRealization c) (P : PositivityInput K) :
    0 ≤ familyMu hm hj hjm K :=
  polynomial_coeff_nonnegative K P _ _ _

theorem familyMu_eq_canonical_coefficient {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    {c : WindowCoxeter (2 * m + 1)} (K : KLRealization c)
    (hgap : (c.system.length (Family.upper hm hj hjm) : ℤ) -
      c.system.length (AffinePermutation.longest (2 * m + 1)) = gapFormula m j) :
    familyMu hm hj hjm K =
      (K.standard.repr (K.canonical (Family.upper hm hj hjm))
        (AffinePermutation.longest (2 * m + 1))) 1 := by
  rw [K.polynomial_normalization, hgap, normalize_family_critical _ hj hjm]
  rfl

/-- The sorted family is right finite-minimal, using the general descent theorem. -/
theorem family_no_finite_right_descent {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2 * m + 1)) (a b : Fin (2 * m + 1))
    (hab : a.val + 1 = b.val) :
    ¬c.system.IsRightDescent (Family.affine hm hj hjm) b := by
  rw [c.finite_descent _ a b hab]
  have hlt := Family.entry_strictMono hm hj hjm (show a < b from by omega)
  omega

theorem inverse_family_no_finite_left_descent {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2 * m + 1)) (a b : Fin (2 * m + 1))
    (hab : a.val + 1 = b.val) :
    ¬c.system.IsLeftDescent (Family.affine hm hj hjm)⁻¹ b := by
  rw [c.system.isLeftDescent_inv_iff]
  exact family_no_finite_right_descent hm hj hjm c a b hab

/-- The ordinary upper endpoint has every finite simple right descent. -/
theorem upper_all_finite_right_descents {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (c : WindowCoxeter (2 * m + 1)) (a b : Fin (2 * m + 1))
    (hab : a.val + 1 = b.val) :
    c.system.IsRightDescent (Family.upper hm hj hjm) b := by
  rw [c.finite_descent _ a b hab, Family.upper_entry, Family.upper_entry]
  apply Family.entry_strictMono hm hj hjm
  have ha := a.isLt
  have hb := b.isLt
  change (2 * m + 1 - (b.val + 1)) < (2 * m + 1 - (a.val + 1))
  omega

end Guralnick.Hecke
