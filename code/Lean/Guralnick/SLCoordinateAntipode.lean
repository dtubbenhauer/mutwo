import Guralnick.SLCoordinateCoalgebra
import Guralnick.SLCoordinateReduced

/-!
# Polynomial inversion and the coordinate antipode

On determinant-one matrices the inverse is the adjugate, whose entries are
polynomials. The antipode constructed here is therefore an actual
coordinate-algebra map, with its action on points proved from that formula.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace Guralnick.SLCoordinate
open RationalCohomology
variable (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι]

/-- The adjugate entry, viewed as a coordinate polynomial. -/
def adjugateCoordinate (i j : ι) : CoordinateAlgebra k ι :=
  (polynomialEvaluation k ι).rangeRestrict
    (Matrix.adjugate (fun a b : ι => (MvPolynomial.X (a,b) : MvPolynomial (ι × ι) k)) i j)

@[simp] theorem adjugateCoordinate_apply (i j : ι) (g : SL ι k) :
    adjugateCoordinate k ι i j g = (g⁻¹ : SL ι k).val i j := by
  change polynomialEvaluation k ι
    (Matrix.adjugate (fun a b : ι => (MvPolynomial.X (a,b) : MvPolynomial (ι × ι) k)) i j) g = _
  rw [polynomialEvaluation_apply, Matrix.SpecialLinearGroup.coe_inv]
  have h := (MvPolynomial.eval (fun ab : ι × ι => (g : Matrix ι ι k) ab.1 ab.2)).map_adjugate
    (fun a b : ι => (MvPolynomial.X (a,b) : MvPolynomial (ι × ι) k))
  have he := congrArg (fun A : Matrix ι ι k => A i j) h
  have hm : Matrix.map
      (fun a b : ι => (MvPolynomial.X (a,b) : MvPolynomial (ι × ι) k))
      (MvPolynomial.eval (fun ab : ι × ι => (g : Matrix ι ι k) ab.1 ab.2)) =
      (g : Matrix ι ι k) := by
    ext a b
    simp
  change (MvPolynomial.eval (fun ab : ι × ι => (g : Matrix ι ι k) ab.1 ab.2))
      (Matrix.adjugate (fun a b : ι => (MvPolynomial.X (a,b) : MvPolynomial (ι × ι) k)) i j) =
      (Matrix.map (fun a b : ι => (MvPolynomial.X (a,b) : MvPolynomial (ι × ι) k))
        (MvPolynomial.eval (fun ab : ι × ι => (g : Matrix ι ι k) ab.1 ab.2))).adjugate i j at he
  rw [hm] at he
  exact he

/-- Substitute the adjugate into an arbitrary matrix-entry polynomial. -/
def inversionPolynomial : MvPolynomial (ι × ι) k →ₐ[k] CoordinateAlgebra k ι :=
  MvPolynomial.aeval fun ij => adjugateCoordinate k ι ij.1 ij.2

@[simp] theorem inversionPolynomial_eval (p : MvPolynomial (ι × ι) k) (g : SL ι k) :
    inversionPolynomial k ι p g = polynomialEvaluation k ι p g⁻¹ := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [inversionPolynomial, polynomialEvaluation]
  | add p q hp hq => simpa using congrArg₂ (·+·) hp hq
  | mul_X p ij hp =>
    rw [map_mul]
    change inversionPolynomial k ι p g * inversionPolynomial k ι (MvPolynomial.X ij) g = _
    rw [hp]
    simp [inversionPolynomial, polynomialEvaluation]

/-- Inversion preserves the actual algebra of coordinate functions. -/
theorem inverse_regular (f : CoordinateAlgebra k ι) :
    (fun g : SL ι k => f g⁻¹) ∈ CoordinateAlgebra k ι := by
  obtain ⟨p, hp⟩ := f.property
  have he : (fun g : SL ι k => f g⁻¹) =
      ((inversionPolynomial k ι p : CoordinateAlgebra k ι) : SL ι k → k) := by
    ext g
    rw [inversionPolynomial_eval]
    exact (congrFun hp g⁻¹).symm
  rw [he]
  exact (inversionPolynomial k ι p).property

/-- The antipode is pullback along the actual inverse matrix map. -/
def antipode : CoordinateAlgebra k ι →ₐ[k] CoordinateAlgebra k ι where
  toFun f := ⟨fun g => f g⁻¹, inverse_regular k ι f⟩
  map_one' := by ext g; rfl
  map_mul' f q := by ext g; rfl
  map_zero' := by ext g; rfl
  map_add' f q := by ext g; rfl
  commutes' r := by ext g; rfl

@[simp] theorem antipode_apply (f : CoordinateAlgebra k ι) (g : SL ι k) :
    antipode k ι f g = f g⁻¹ := rfl

@[simp] theorem antipode_involutive (f : CoordinateAlgebra k ι) :
    antipode k ι (antipode k ι f) = f := by
  ext g
  simp

end Guralnick.SLCoordinate
