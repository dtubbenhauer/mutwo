import Guralnick.SLCoordinateTensor
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The reduced coordinate algebra of the classical SL variety

The coordinate algebra is the image of polynomial evaluation on actual
matrices of determinant one. The first isomorphism theorem identifies it
with the polynomial ring modulo the vanishing ideal of that algebraic set.
Over an algebraically closed field, Nullstellensatz further identifies this
ideal with the radical of the determinant equation. The companion file
`SLCoordinateReduced` proves that this principal ideal is already radical.
-/
noncomputable section
open scoped TensorProduct

namespace Guralnick.SLCoordinate
open RationalCohomology

variable (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι]

/-- Restriction of ordinary matrix-entry polynomials to actual SL points. -/
def polynomialEvaluation : MvPolynomial (ι × ι) k →ₐ[k] (SL ι k → k) :=
  MvPolynomial.aeval (fun ij g => (g : Matrix ι ι k) ij.1 ij.2)

@[simp] theorem polynomialEvaluation_apply (p : MvPolynomial (ι × ι) k) (g : SL ι k) :
    polynomialEvaluation k ι p g =
      MvPolynomial.eval (fun ij => (g : Matrix ι ι k) ij.1 ij.2) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [polynomialEvaluation]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, Pi.mul_apply, hp, MvPolynomial.eval_mul]
    congr 1
    simp [polynomialEvaluation]

/-- The coordinate algebra of the classical reduced matrix variety SL. -/
abbrev CoordinateAlgebra : Subalgebra k (SL ι k → k) :=
  (polynomialEvaluation k ι).range

instance (priority := 2000) coordinateCommRing : CommRing (CoordinateAlgebra k ι) :=
  (CoordinateAlgebra k ι).toCommRing

instance (priority := 2000) coordinateAlgebra : Algebra k (CoordinateAlgebra k ι) :=
  (CoordinateAlgebra k ι).algebra

instance (priority := 2000) coordinateModule : Module k (CoordinateAlgebra k ι) :=
  (CoordinateAlgebra k ι).instModuleSubtypeMem

instance (priority := 2000) coordinateAddCommGroup : AddCommGroup (CoordinateAlgebra k ι) :=
  (CoordinateAlgebra k ι).toCommRing.toAddCommGroup

instance (priority := 2000) coordinateAddCommMonoid : AddCommMonoid (CoordinateAlgebra k ι) :=
  (coordinateAddCommGroup k ι).toAddCommMonoid

instance : CoeFun (CoordinateAlgebra k ι) (fun _ => SL ι k → k) := ⟨Subtype.val⟩

@[simp] theorem mem_coordinate_iff (f : SL ι k → k) :
    f ∈ CoordinateAlgebra k ι ↔ f ∈ regularMaps k ι k := by
  rw [regular_scalar_iff]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, fun g => (congrFun hp g).symm.trans (polynomialEvaluation_apply k ι p g)⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, funext fun g => (polynomialEvaluation_apply k ι p g).trans (hp g).symm⟩

/-- The actual matrix-entry coordinate function. -/
def coordinate (i j : ι) : CoordinateAlgebra k ι :=
  (polynomialEvaluation k ι).rangeRestrict (MvPolynomial.X (i,j))

@[simp] theorem coordinate_apply (i j : ι) (g : SL ι k) :
    coordinate k ι i j g = (g : Matrix ι ι k) i j := by
  simp [coordinate]

/-- The determinant-one algebraic set in affine matrix space. -/
def determinantOnePoints : Set ((ι × ι) → k) :=
  {x | Matrix.det (fun i j => x (i,j)) = 1}

/-- The vanishing ideal, rather than a chosen polynomial presentation. -/
def vanishingIdeal : Ideal (MvPolynomial (ι × ι) k) :=
  MvPolynomial.vanishingIdeal (determinantOnePoints k ι)

theorem evaluation_ker_eq_vanishingIdeal :
    RingHom.ker (polynomialEvaluation k ι) = vanishingIdeal k ι := by
  ext p
  simp only [RingHom.mem_ker, vanishingIdeal, MvPolynomial.mem_vanishingIdeal_iff,
    funext_iff, polynomialEvaluation_apply, Pi.zero_apply]
  constructor
  · intro h x hx
    exact h ⟨(fun i j => x (i,j)), hx⟩
  · intro h g
    exact h (fun ij => (g : Matrix ι ι k) ij.1 ij.2) g.property

/-- A genuine quotient-to-functions coordinate-algebra equivalence. -/
def quotientVanishingEquiv :
    (MvPolynomial (ι × ι) k ⧸ vanishingIdeal k ι) ≃ₐ[k] CoordinateAlgebra k ι :=
  (Ideal.quotientEquivAlgOfEq k (evaluation_ker_eq_vanishingIdeal k ι).symm).trans
    (Ideal.quotientKerEquivRange (polynomialEvaluation k ι))

/-- The universal determinant in the independent matrix variables. -/
def determinantPolynomial : MvPolynomial (ι × ι) k :=
  Matrix.det (fun i j => MvPolynomial.X (i,j))

@[simp] theorem eval_determinantPolynomial (x : (ι × ι) → k) :
    MvPolynomial.eval x (determinantPolynomial k ι) =
      Matrix.det (fun i j => x (i,j)) := by
  rw [determinantPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp

/-- The usual single defining equation of SL. -/
def determinantIdeal : Ideal (MvPolynomial (ι × ι) k) :=
  Ideal.span {determinantPolynomial k ι - 1}

theorem zeroLocus_determinantIdeal :
    MvPolynomial.zeroLocus (determinantIdeal k ι) = determinantOnePoints k ι := by
  ext x
  simp [determinantIdeal, MvPolynomial.zeroLocus_span, determinantOnePoints, sub_eq_zero]

/-- Nullstellensatz ties the actual reduced variety to the determinant equation.
This is an equality with the radical, not an assertion that the equation
has already been proved radical. -/
theorem vanishingIdeal_eq_radical [IsAlgClosed k] :
    vanishingIdeal k ι = (determinantIdeal k ι).radical := by
  rw [vanishingIdeal, ← zeroLocus_determinantIdeal,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]

/-- The reduced determinant presentation agrees with actual polynomial functions. -/
def quotientRadicalEquiv [IsAlgClosed k] :
    (MvPolynomial (ι × ι) k ⧸ (determinantIdeal k ι).radical) ≃ₐ[k]
      CoordinateAlgebra k ι :=
  (Ideal.quotientEquivAlgOfEq k (vanishingIdeal_eq_radical k ι).symm).trans
    (quotientVanishingEquiv k ι)

end Guralnick.SLCoordinate
