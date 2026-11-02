import Guralnick.SLCoordinateAlgebra
import Mathlib.Algebra.Algebra.Pi

/-!
# The matrix multiplication coproduct on the reduced coordinate algebra

The formula Δ(xᵢⱼ)=∑ₐ xᵢₐ⊗xₐⱼ is first defined on polynomials. Faithfulness
of tensor evaluation proves that it descends to actual coordinate functions.
The construction therefore proves descent; it does not assume that a choice
of polynomial representative respects products.
-/
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
noncomputable section
open scoped TensorProduct BigOperators
namespace Guralnick.SLCoordinate
open RationalCohomology
variable (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι]

/-- Evaluation at an actual determinant-one matrix is an algebra homomorphism. -/
def evaluationAt (g : SL ι k) : CoordinateAlgebra k ι →ₐ[k] k :=
  (Pi.evalAlgHom k (fun _ : SL ι k => k) g).comp (CoordinateAlgebra k ι).val

@[simp] theorem evaluationAt_apply (g : SL ι k) (f : CoordinateAlgebra k ι) :
    evaluationAt k ι g f = f g := rfl

/-- A tensor of coordinate functions evaluated on an ordered pair of matrices. -/
def pairEvaluation : CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι →ₐ[k]
    (SL ι k × SL ι k → k) :=
  Pi.algHom k (fun _ => k) fun gh =>
    Algebra.TensorProduct.lift (evaluationAt k ι gh.1) (evaluationAt k ι gh.2)
      (fun _ _ => Commute.all _ _)

@[simp] theorem pairEvaluation_tmul (f g : CoordinateAlgebra k ι) (x y : SL ι k) :
    pairEvaluation k ι (f ⊗ₜ[k] g) (x,y) = f x * g y := rfl

theorem pairEvaluation_toLinearMap : (pairEvaluation k ι).toLinearMap =
    tensorEvaluation (CoordinateAlgebra k ι).val.toLinearMap
      (CoordinateAlgebra k ι).val.toLinearMap := by
  apply TensorProduct.ext
  ext f g
  rfl

/-- Equality of functions on pairs proves equality of coordinate tensors. -/
theorem pairEvaluation_injective : Function.Injective (pairEvaluation k ι) := by
  change Function.Injective (pairEvaluation k ι).toLinearMap
  rw [pairEvaluation_toLinearMap]
  exact tensorEvaluation_injective _ _ Subtype.val_injective Subtype.val_injective

/-- Explicit substitution supplied by ordinary matrix multiplication. -/
def multiplicationPolynomial : MvPolynomial (ι × ι) k →ₐ[k]
    CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι :=
  MvPolynomial.aeval fun ij => ∑ a : ι, coordinate k ι ij.1 a ⊗ₜ[k] coordinate k ι a ij.2

@[simp] theorem pairEvaluation_multiplicationPolynomial
    (p : MvPolynomial (ι × ι) k) (g h : SL ι k) :
    pairEvaluation k ι (multiplicationPolynomial k ι p) (g,h) =
      polynomialEvaluation k ι p (g*h) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [multiplicationPolynomial, polynomialEvaluation]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p ij hp =>
    simp only [map_mul, Pi.mul_apply, hp]
    congr 1
    simp [multiplicationPolynomial, polynomialEvaluation, Matrix.mul_apply]

/-- A chosen representative is used only to construct the coproduct;
`comultiplicationValue_eval` and faithful evaluation remove the choice. -/
def comultiplicationValue (f : CoordinateAlgebra k ι) :
    CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι :=
  multiplicationPolynomial k ι (Classical.choose f.property)

@[simp] theorem comultiplicationValue_eval (f : CoordinateAlgebra k ι) (g h : SL ι k) :
    pairEvaluation k ι (comultiplicationValue k ι f) (g,h) = f (g*h) := by
  rw [comultiplicationValue, pairEvaluation_multiplicationPolynomial]
  exact congrFun (Classical.choose_spec f.property) (g*h)

/-- The coproduct on actual coordinate functions, with proved algebra laws. -/
def comultiplication : CoordinateAlgebra k ι →ₐ[k]
    CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι where
  toFun := comultiplicationValue k ι
  map_one' := by
    apply pairEvaluation_injective k ι
    ext gh
    rcases gh with ⟨g,h⟩
    simp
  map_mul' f q := by
    apply pairEvaluation_injective k ι
    ext gh
    rcases gh with ⟨g,h⟩
    simp
  map_zero' := by
    apply pairEvaluation_injective k ι
    ext gh
    rcases gh with ⟨g,h⟩
    simp
  map_add' f q := by
    apply pairEvaluation_injective k ι
    ext gh
    rcases gh with ⟨g,h⟩
    simp
  commutes' r := by
    apply pairEvaluation_injective k ι
    ext gh
    rcases gh with ⟨g,h⟩
    simp

@[simp] theorem comultiplication_eval (f : CoordinateAlgebra k ι) (g h : SL ι k) :
    pairEvaluation k ι (comultiplication k ι f) (g,h) = f (g*h) :=
  comultiplicationValue_eval k ι f g h

/-- Evaluation at the identity matrix supplies the counit. -/
def counit : CoordinateAlgebra k ι →ₐ[k] k := evaluationAt k ι 1

@[simp] theorem counit_apply (f : CoordinateAlgebra k ι) : counit k ι f = f 1 := rfl

/-- The familiar matrix-coordinate coproduct is a theorem of the construction. -/
theorem comultiplication_coordinate (i j : ι) :
    comultiplication k ι (coordinate k ι i j) =
      ∑ a : ι, coordinate k ι i a ⊗ₜ[k] coordinate k ι a j := by
  apply pairEvaluation_injective k ι
  ext gh
  rcases gh with ⟨g,h⟩
  simp [Matrix.mul_apply]

end Guralnick.SLCoordinate
