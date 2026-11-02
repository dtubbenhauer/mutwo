import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-!
# Polynomial representations of SL and regular first cohomology

The objects here are actual representations of the matrix group SL, and
actual vector-valued polynomials in its matrix entries. `RationalH1` is the
space of polynomial 1-cocycles modulo genuine coboundaries. For a polynomial
representation all coboundaries are proved polynomial. Its comparison with
derived-functor rational algebraic-group cohomology is a separate standard
literature theorem, not a definition or an axiom of this development.

The polynomial-function/coordinate-algebra step of that comparison is now
proved in `RationalCoordinateH1` and `RationalCoordinateRepresentations`,
using the exact determinant quotient and Hopf algebra in `SLCoordinate*`.
The remaining cited theorem concerns the derived-functor interpretation.

The precise primary reference for that comparison is J. C. Jantzen,
*Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985), §§4.14–4.16,
especially Proposition 4.16, printed p. 79:
https://archive.mpim-bonn.mpg.de/id/eprint/607/1/preprint_1985_9.pdf .
There the regular inhomogeneous cochains compute derived rational cohomology.
This numbering refers to the checked 1985 preprint, not to a later edition.

The intended algebraic-group interpretation is over an algebraically closed
field. The function-space constructions are also defined over other fields;
there they are not by themselves a scheme-theoretic rational-representation
category. In particular, a literature application must retain the field
hypotheses, rather than infer algebraic rationality from arbitrary finite-field
point functions.
-/

noncomputable section
open scoped BigOperators

namespace Guralnick.RationalCohomology

variable {k : Type} [Field k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev SL (ι : Type) (k : Type) [Fintype ι] [DecidableEq ι] [Field k] :=
  Matrix.SpecialLinearGroup ι k

/-- A vector-valued polynomial: finitely many monomials, each with a
coefficient in the actual coefficient module. -/
abbrev VectorPolynomial (ι : Type) (V : Type) [Zero V] := ((ι × ι) →₀ ℕ) →₀ V

/-- Evaluate one scalar monomial on the matrix entries of an SL element. -/
def monomialValue (d : (ι × ι) →₀ ℕ) (g : SL ι k) : k :=
  d.prod (fun ij e => (g : Matrix ι ι k) ij.1 ij.2 ^ e)

@[simp] theorem monomialValue_zero (g : SL ι k) : monomialValue 0 g = 1 := by
  simp [monomialValue]

variable {V : Type} [AddCommGroup V] [Module k V]
variable {W : Type} [AddCommGroup W] [Module k W]

/-- The linear contribution of one monomial to a vector polynomial. -/
def monomialEvaluation (d : (ι × ι) →₀ ℕ) : V →ₗ[k] (SL ι k → V) where
  toFun a g := monomialValue d g • a
  map_add' a b := by ext g; simp [smul_add]
  map_smul' c a := by ext g; simp [smul_smul, mul_comm]

/-- Evaluation of a vector polynomial, as a linear map into actual functions. -/
def evaluation : VectorPolynomial ι V →ₗ[k] (SL ι k → V) :=
  Finsupp.lsum k (monomialEvaluation (k := k))

@[simp] theorem evaluation_single (d : (ι × ι) →₀ ℕ) (a : V) (g : SL ι k) :
    evaluation (Finsupp.single d a) g = monomialValue d g • a := by
  rw [evaluation, Finsupp.lsum_single]
  rfl

/-- Polynomial maps on SL, independent of a choice of basis in the target. -/
def regularMaps (k : Type) (ι : Type) (V : Type)
    [Field k] [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module k V] :
    Submodule k (SL ι k → V) := LinearMap.range evaluation

theorem regular_constant (a : V) : (fun _ : SL ι k => a) ∈ regularMaps k ι V := by
  refine ⟨Finsupp.single 0 a, ?_⟩
  ext g
  simp

/-- Linear maps commute with polynomial evaluation. -/
theorem evaluation_map (L : V →ₗ[k] W) (p : VectorPolynomial ι V) :
    evaluation (Finsupp.mapRange.linearMap L p) = fun g : SL ι k => L (evaluation p g) := by
  induction p using Finsupp.induction_linear with
  | zero => ext g; simp
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    ext g
    simp
  | single d a =>
    ext g
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      evaluation_single, map_smul]

theorem regular_linear_map (L : V →ₗ[k] W) {f : SL ι k → V}
    (hf : f ∈ regularMaps k ι V) : (fun g => L (f g)) ∈ regularMaps k ι W := by
  obtain ⟨p, rfl⟩ := hf
  exact ⟨Finsupp.mapRange.linearMap L p, evaluation_map L p⟩

/-- Scalar vector polynomials are ordinary multivariate polynomials. -/
theorem scalar_evaluation_eq (p : MvPolynomial (ι × ι) k) (g : SL ι k) :
    evaluation (V := k) p g =
      MvPolynomial.eval (fun ij => (g : Matrix ι ι k) ij.1 ij.2) p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, MvPolynomial.eval_add]
    simp only [Pi.add_apply, hp, hq]
  | monomial d a =>
    change evaluation (Finsupp.single d a) g = _
    rw [evaluation_single, MvPolynomial.eval_monomial]
    simp [monomialValue, smul_eq_mul, mul_comm]

/-- Each scalar coordinate of a regular vector map is represented by an
ordinary multivariate polynomial in the entries of the SL matrix. -/
theorem regular_scalar_coordinates {f : SL ι k → V} (hf : f ∈ regularMaps k ι V)
    (L : V →ₗ[k] k) : ∃ p : MvPolynomial (ι × ι) k,
      ∀ g : SL ι k, L (f g) =
        MvPolynomial.eval (fun ij => (g : Matrix ι ι k) ij.1 ij.2) p := by
  obtain ⟨p, hp⟩ := regular_linear_map L hf
  refine ⟨p, ?_⟩
  intro g
  rw [← congrFun hp g, scalar_evaluation_eq]

theorem regular_scalar_iff (f : SL ι k → k) :
    f ∈ regularMaps k ι k ↔ ∃ p : MvPolynomial (ι × ι) k,
      ∀ g : SL ι k, f g =
        MvPolynomial.eval (fun ij => (g : Matrix ι ι k) ij.1 ij.2) p := by
  constructor
  · intro hf
    simpa using regular_scalar_coordinates hf (LinearMap.id : k →ₗ[k] k)
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    ext g
    rw [scalar_evaluation_eq, hp]

/-- Finite-dimensional regularity is equivalent to regularity of the
coordinates in any basis. -/
theorem regular_iff_coordinates {κ : Type} [Fintype κ] (b : Basis κ k V)
    (f : SL ι k → V) :
    f ∈ regularMaps k ι V ↔
      ∀ i, (fun g => b.coord i (f g)) ∈ regularMaps k ι k := by
  constructor
  · intro hf i
    exact regular_linear_map (b.coord i) hf
  · intro hf
    have he : f = ∑ i, (fun g : SL ι k => b.coord i (f g) • b i) := by
      ext g
      simpa using (b.sum_repr (f g)).symm
    rw [he]
    apply (regularMaps k ι V).sum_mem
    intro i hi
    exact regular_linear_map (LinearMap.toSpanSingleton k V (b i)) (hf i)

/-- Polynomiality of the actual action maps. In finite dimension this is
exactly the matrix-coefficient condition in any basis. -/
def IsPolynomialRepresentation (A : Rep k (SL ι k)) : Prop :=
  ∀ a : A, (fun g => A.ρ g a) ∈ regularMaps k ι A

theorem isPolynomialRepresentation_iff_basis {A : Rep k (SL ι k)}
    {κ : Type} [Fintype κ] (b : Basis κ k A) :
    IsPolynomialRepresentation A ↔
      ∀ j, (fun g => A.ρ g (b j)) ∈ regularMaps k ι A := by
  constructor
  · intro h j
    exact h (b j)
  · intro h a
    have he : (fun g => A.ρ g a) =
        ∑ j, b.repr a j • (fun g => A.ρ g (b j)) := by
      ext g
      simpa using congrArg (A.ρ g) (b.sum_repr a).symm
    rw [he]
    exact (regularMaps k ι A).sum_mem (fun j _ =>
      (regularMaps k ι A).smul_mem _ (h j))

/-- The usual matrix-coefficient definition of a polynomial representation,
proved equivalent to the basis-independent predicate used by this file. -/
theorem isPolynomialRepresentation_iff_matrix_coefficients {A : Rep k (SL ι k)}
    {κ : Type} [Fintype κ] (b : Basis κ k A) :
    IsPolynomialRepresentation A ↔
      ∀ i j, ∃ p : MvPolynomial (ι × ι) k, ∀ g : SL ι k,
        b.coord i (A.ρ g (b j)) =
          MvPolynomial.eval (fun ij => (g : Matrix ι ι k) ij.1 ij.2) p := by
  rw [isPolynomialRepresentation_iff_basis b]
  simp only [regular_iff_coordinates b, regular_scalar_iff]
  exact forall_comm

/-- Actual polynomial 1-cocycles, with the usual crossed-homomorphism law. -/
def rationalCocycles (A : Rep k (SL ι k)) : Submodule k (SL ι k → A) :=
  regularMaps k ι A ⊓ groupCohomology.oneCocycles A

theorem mem_rationalCocycles_iff (A : Rep k (SL ι k)) (f : SL ι k → A) :
    f ∈ rationalCocycles A ↔ f ∈ regularMaps k ι A ∧
      ∀ g h : SL ι k, f (g*h) = A.ρ g (f h) + f g := by
  simp only [rationalCocycles, Submodule.mem_inf, groupCohomology.mem_oneCocycles_iff]

/-- Every actual coboundary of a polynomial representation is regular. -/
theorem dZero_regular {A : Rep k (SL ι k)} (hA : IsPolynomialRepresentation A) (a : A) :
    groupCohomology.dZero A a ∈ regularMaps k ι A := by
  exact (regularMaps k ι A).sub_mem (hA a) (regular_constant a)

theorem coboundaries_le_regular {A : Rep k (SL ι k)} (hA : IsPolynomialRepresentation A) :
    groupCohomology.oneCoboundaries A ≤ regularMaps k ι A := by
  rintro f ⟨a, rfl⟩
  exact dZero_regular hA a

/-- Actual coboundaries, regarded as a submodule of the regular cocycles.
For a polynomial representation none are lost: see `coboundaries_le_regular`. -/
def rationalBoundaries (A : Rep k (SL ι k)) : Submodule k (rationalCocycles A) :=
  (groupCohomology.oneCoboundaries A).comap (rationalCocycles A).subtype

/-- Regular 1-cocycles modulo coboundaries. This is a quotient vector space,
not a number defined from KL data. -/
abbrev RationalH1 (A : Rep k (SL ι k)) :=
  (rationalCocycles A) ⧸ rationalBoundaries A

/-- The usual coboundary map with codomain restricted to regular cocycles. -/
def regularCoboundary {A : Rep k (SL ι k)} (hA : IsPolynomialRepresentation A) :
    A →ₗ[k] rationalCocycles A :=
  (groupCohomology.dZero A).hom.codRestrict (rationalCocycles A)
    (fun a => ⟨dZero_regular hA a, groupCohomology.dZero_apply_mem_oneCocycles a⟩)

/-- The quotient uses exactly the image of the genuine coboundary map. -/
theorem rationalBoundaries_eq_range {A : Rep k (SL ι k)}
    (hA : IsPolynomialRepresentation A) :
    rationalBoundaries A = LinearMap.range (regularCoboundary hA) := by
  ext f
  constructor
  · intro hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨a, ?_⟩
    exact Subtype.ext ha
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

/-- Forget regularity, retaining the actual 1-cocycle. -/
def forgetRegularity (A : Rep k (SL ι k)) :
    rationalCocycles A →ₗ[k] groupCohomology.oneCocycles A :=
  Submodule.inclusion inf_le_right

/-- Class of a regular cocycle in ordinary abstract-group cohomology. -/
def abstractProjection (A : Rep k (SL ι k)) :
    rationalCocycles A →ₗ[k] groupCohomology.H1 A :=
  (groupCohomology.H1π A).hom.comp (forgetRegularity A)

theorem abstractProjection_kernel (A : Rep k (SL ι k)) :
    LinearMap.ker (abstractProjection A) = rationalBoundaries A := by
  ext f
  change groupCohomology.H1π A (forgetRegularity A f) = 0 ↔ _
  rw [groupCohomology.H1π_eq_zero_iff]
  rfl

/-- Natural map to the actual abstract-group first cohomology. It is not
asserted to be surjective; regular cohomology need not equal abstract H1. -/
def toAbstractH1 (A : Rep k (SL ι k)) : RationalH1 A →ₗ[k] groupCohomology.H1 A :=
  (rationalBoundaries A).liftQ (abstractProjection A)
    (abstractProjection_kernel A).ge

theorem toAbstractH1_injective (A : Rep k (SL ι k)) :
    Function.Injective (toAbstractH1 A) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (abstractProjection_kernel A).le

open CategoryTheory
variable {G : Type} [Group G]

/-- Restriction of the actual representation along a group homomorphism. -/
abbrev restrictedRepresentation (f : G →* SL ι k) (A : Rep k (SL ι k)) : Rep k G :=
  (Action.res (ModuleCat k) f).obj A

/-- Restrict a regular algebraic cocycle by composing its actual function
with the group homomorphism. No cohomological dimension is supplied. -/
def restrictionOneCocycles (f : G →* SL ι k) (A : Rep k (SL ι k)) :
    rationalCocycles A →ₗ[k] groupCohomology.oneCocycles (restrictedRepresentation f A) where
  toFun z := ⟨fun g => z.val (f g), by
    rw [groupCohomology.mem_oneCocycles_iff]
    intro g h
    have hz := (groupCohomology.mem_oneCocycles_iff z.val).mp z.property.2
    simpa only [map_mul] using hz (f g) (f h)⟩
  map_add' a b := rfl
  map_smul' c a := rfl

@[simp] theorem restrictionOneCocycles_apply (f : G →* SL ι k)
    (A : Rep k (SL ι k)) (z : rationalCocycles A) (g : G) :
    restrictionOneCocycles f A z g = z.val (f g) := rfl

/-- The same vector defines the restricted coboundary. -/
theorem restriction_coboundary {A : Rep k (SL ι k)}
    (hA : IsPolynomialRepresentation A) (f : G →* SL ι k) (a : A) :
    (restrictionOneCocycles f A (regularCoboundary hA a) : G → A) =
      groupCohomology.dZero (restrictedRepresentation f A) a := rfl

/-- Restriction followed by the ordinary cocycle-to-cohomology projection. -/
def restrictionProjection (f : G →* SL ι k) (A : Rep k (SL ι k)) :
    rationalCocycles A →ₗ[k] groupCohomology.H1 (restrictedRepresentation f A) :=
  (groupCohomology.H1π (restrictedRepresentation f A)).hom.comp (restrictionOneCocycles f A)

theorem rationalBoundaries_le_restriction_kernel (f : G →* SL ι k)
    (A : Rep k (SL ι k)) :
    rationalBoundaries A ≤ LinearMap.ker (restrictionProjection f A) := by
  intro z hz
  change groupCohomology.H1π (restrictedRepresentation f A) (restrictionOneCocycles f A z) = 0
  rw [groupCohomology.H1π_eq_zero_iff]
  obtain ⟨a, ha⟩ := hz
  refine ⟨a, ?_⟩
  ext g
  exact congrFun ha (f g)

/-- The specified natural restriction map from regular algebraic H1 to
actual ordinary group H1. A BNP input should assert bijectivity of this map
under its hypotheses, rather than merely equality of two arbitrary numbers. -/
def restrictionH1 (f : G →* SL ι k) (A : Rep k (SL ι k)) :
    RationalH1 A →ₗ[k] groupCohomology.H1 (restrictedRepresentation f A) :=
  (rationalBoundaries A).liftQ (restrictionProjection f A)
    (rationalBoundaries_le_restriction_kernel f A)

@[simp] theorem restrictionH1_mk (f : G →* SL ι k) (A : Rep k (SL ι k))
    (z : rationalCocycles A) :
    restrictionH1 f A (Submodule.Quotient.mk z) =
      groupCohomology.H1π (restrictedRepresentation f A) (restrictionOneCocycles f A z) := rfl

theorem restrictionOneCocycles_eq_map (f : G →* SL ι k) (A : Rep k (SL ι k))
    (z : rationalCocycles A) :
    restrictionOneCocycles f A z =
      groupCohomology.mapOneCocycles f (𝟙 (restrictedRepresentation f A)) (forgetRegularity A z) := by
  apply Subtype.ext
  rfl

/-- Compatibility with mathlib's independently defined cohomology functor. -/
theorem restrictionH1_eq_map (f : G →* SL ι k) (A : Rep k (SL ι k)) :
    restrictionH1 f A =
      (groupCohomology.map f (𝟙 (restrictedRepresentation f A)) 1).hom.comp (toAbstractH1 A) := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro z
  rw [restrictionH1_mk]
  change groupCohomology.H1π (restrictedRepresentation f A) (restrictionOneCocycles f A z) =
    groupCohomology.map f (𝟙 (restrictedRepresentation f A)) 1
      (groupCohomology.H1π A (forgetRegularity A z))
  rw [restrictionOneCocycles_eq_map]
  exact (CategoryTheory.congr_fun (groupCohomology.H1π_comp_map f
    (𝟙 (restrictedRepresentation f A))) (forgetRegularity A z)).symm

end Guralnick.RationalCohomology
