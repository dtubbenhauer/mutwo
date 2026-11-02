import Guralnick.CoordinateTensor
import Guralnick.SLCoordinateAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Coordinate tensors for rational representations and cochains

The coordinate algebra is the polynomial quotient by the vanishing ideal of
the determinant-one affine variety, as constructed in `SLCoordinateAlgebra`.
Here its genuine tensor-valued degree-one cochains are compared with the
polynomial function model used by the existing cohomological transfer.
-/

noncomputable section
open scoped TensorProduct BigOperators
set_option synthInstance.maxHeartbeats 200000

namespace Guralnick.RationalCoordinate
open RationalCohomology SLCoordinate

variable {k ι V : Type} [Field k] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

abbrev CochainsOne (k ι V : Type) [Field k] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module k V] := V ⊗[k] CoordinateAlgebra k ι

def evaluateOne : CochainsOne k ι V →ₗ[k] (SL ι k → V) :=
  CoordinateTensor.evaluation (CoordinateAlgebra k ι).toSubmodule

omit [FiniteDimensional k V] in
@[simp] theorem evaluateOne_tmul (a : V) (f : CoordinateAlgebra k ι) (g : SL ι k) :
    evaluateOne (a ⊗ₜ[k] f) g = f g • a := rfl

theorem coordinateRegular_eq :
    CoordinateTensor.regular (CoordinateAlgebra k ι).toSubmodule
      (Module.finBasis k V) = regularMaps k ι V := by
  ext f
  change (∀ i, (fun g => (Module.finBasis k V).coord i (f g)) ∈
    CoordinateAlgebra k ι) ↔ _
  simp only [mem_coordinate_iff]
  exact (regular_iff_coordinates (Module.finBasis k V) f).symm

/-- Actual finite-dimensional regular maps are coordinate-algebra tensors. -/
def cochainEquiv : CochainsOne k ι V ≃ₗ[k] regularMaps k ι V :=
  (CoordinateTensor.regularEquiv (CoordinateAlgebra k ι).toSubmodule
    (Module.finBasis k V)).trans (LinearEquiv.ofEq _ _ coordinateRegular_eq)

@[simp] theorem cochainEquiv_val (t : CochainsOne k ι V) :
    (cochainEquiv t).val = evaluateOne t := rfl

theorem evaluateOne_injective : Function.Injective (evaluateOne (k := k) (ι := ι) (V := V)) :=
  CoordinateTensor.evaluation_injective _ (Module.finBasis k V)

@[simp] theorem evaluateOne_cochainEquiv_symm (f : regularMaps k ι V) :
    evaluateOne (cochainEquiv.symm f) = f.val := by
  exact congrArg Subtype.val (cochainEquiv.apply_symm_apply f)

variable {A : Rep k (SL ι k)} [FiniteDimensional k A]

def actionRegular (hA : IsPolynomialRepresentation A) : A →ₗ[k] regularMaps k ι A where
  toFun a := ⟨fun g => A.ρ g a, hA a⟩
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

/-- The action coaction is a genuine linear map into `A ⊗ k[SL]`.
Its construction uses the proved tensor/function equivalence. -/
def coaction (hA : IsPolynomialRepresentation A) : A →ₗ[k] CochainsOne k ι A :=
  (cochainEquiv (k := k) (ι := ι) (V := A)).symm.toLinearMap.comp
    (actionRegular hA)

@[simp] theorem evaluateOne_coaction (hA : IsPolynomialRepresentation A) (a : A) :
    evaluateOne (coaction hA a) = fun g => A.ρ g a := by
  exact evaluateOne_cochainEquiv_symm (k := k) (ι := ι) (V := A)
    ⟨fun g => A.ρ g a, hA a⟩

/-- Evaluation at the identity proves the counit identity. -/
theorem coaction_counit (hA : IsPolynomialRepresentation A) (a : A) :
    evaluateOne (coaction hA a) 1 = a := by
  rw [evaluateOne_coaction]
  simp

abbrev CochainsTwo (k ι V : Type) [Field k] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module k V] :=
  V ⊗[k] (CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι)

def scalarEvaluateTwo :
    CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι →ₗ[k] (SL ι k × SL ι k → k) :=
  tensorEvaluation (CoordinateAlgebra k ι).toSubmodule.subtype
    (CoordinateAlgebra k ι).toSubmodule.subtype

theorem scalarEvaluateTwo_injective :
    Function.Injective (scalarEvaluateTwo (k := k) (ι := ι)) :=
  tensorEvaluation_injective _ _ Subtype.val_injective Subtype.val_injective

def evaluateTwo : CochainsTwo k ι V →ₗ[k] (SL ι k × SL ι k → V) :=
  CoordinateTensor.linearEvaluation scalarEvaluateTwo

omit [FiniteDimensional k V] in
@[simp] theorem evaluateTwo_tmul (a : V)
    (f : CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι) (g h : SL ι k) :
    evaluateTwo (a ⊗ₜ[k] f) (g,h) = scalarEvaluateTwo f (g,h) • a := rfl

@[simp] theorem scalarEvaluateTwo_tmul (f h : CoordinateAlgebra k ι) (g g' : SL ι k) :
    scalarEvaluateTwo (f ⊗ₜ[k] h) (g,g') = f g * h g' := rfl

theorem evaluateTwo_injective : Function.Injective (evaluateTwo (k := k) (ι := ι) (V := V)) :=
  CoordinateTensor.linearEvaluation_injective _ scalarEvaluateTwo_injective
    (Module.finBasis k V)

omit [FiniteDimensional k V] in
theorem evaluateTwo_assoc_tmul (t : CochainsOne k ι V) (f : CoordinateAlgebra k ι)
    (g h : SL ι k) :
    evaluateTwo ((TensorProduct.assoc k V (CoordinateAlgebra k ι)
      (CoordinateAlgebra k ι)) (t ⊗ₜ[k] f)) (g,h) = f h • evaluateOne t g := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp [TensorProduct.add_tmul, ht, hu, smul_add]
  | tmul a r => simp [mul_smul, mul_comm]

/-- The first term of the regular bar differential, induced by the coaction. -/
def actionTerm (hA : IsPolynomialRepresentation A) :
    CochainsOne k ι A →ₗ[k] CochainsTwo k ι A :=
  (TensorProduct.assoc k A (CoordinateAlgebra k ι) (CoordinateAlgebra k ι)).toLinearMap.comp
    (TensorProduct.map (coaction hA) LinearMap.id)

theorem evaluateTwo_actionTerm (hA : IsPolynomialRepresentation A)
    (t : CochainsOne k ι A) (g h : SL ι k) :
    evaluateTwo (actionTerm hA t) (g,h) = A.ρ g (evaluateOne t h) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp [ht, hu]
  | tmul a f =>
    simp only [actionTerm, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearEquiv.coe_coe, evaluateTwo_assoc_tmul,
      evaluateOne_coaction, evaluateOne_tmul, map_smul]

/-- Insertion of the coordinate-algebra unit in the last factor. -/
def appendUnit : CochainsOne k ι V →ₗ[k] CochainsTwo k ι V :=
  TensorProduct.map LinearMap.id
    ((TensorProduct.mk k (CoordinateAlgebra k ι) (CoordinateAlgebra k ι)).flip 1)

omit [FiniteDimensional k V] in
theorem evaluateTwo_appendUnit (t : CochainsOne k ι V) (g h : SL ι k) :
    evaluateTwo (appendUnit t) (g,h) = evaluateOne t g := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp [ht, hu]
  | tmul a f => simp [appendUnit]

/-- The constant degree-one cochain associated with a vector. -/
def constantOne : V →ₗ[k] CochainsOne k ι V :=
  (TensorProduct.mk k V (CoordinateAlgebra k ι)).flip 1

omit [FiniteDimensional k V] in
@[simp] theorem evaluateOne_constantOne (a : V) (g : SL ι k) :
    evaluateOne (constantOne a) g = a := by simp [constantOne]

/-- The degree-zero differential, in tensor coordinates. -/
def differentialZero (hA : IsPolynomialRepresentation A) : A →ₗ[k] CochainsOne k ι A :=
  coaction hA - constantOne

@[simp] theorem evaluateOne_differentialZero (hA : IsPolynomialRepresentation A)
    (a : A) (g : SL ι k) :
    evaluateOne (differentialZero hA a) g = A.ρ g a - a := by
  simp [differentialZero]

section Comultiplication
variable (Δ : CoordinateAlgebra k ι →ₗ[k]
  CoordinateAlgebra k ι ⊗[k] CoordinateAlgebra k ι)
variable (hΔ : ∀ (f : CoordinateAlgebra k ι) (g h : SL ι k),
  scalarEvaluateTwo (Δ f) (g,h) = f (g*h))
include hΔ

omit [FiniteDimensional k V] in
theorem evaluateTwo_map_comultiplication (t : CochainsOne k ι V) (g h : SL ι k) :
    evaluateTwo (TensorProduct.map LinearMap.id Δ t) (g,h) = evaluateOne t (g*h) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp [ht, hu]
  | tmul a f => simp [hΔ]

/-- The coassociativity identity is proved from the actual group action and
faithful evaluation of the genuine two-coordinate tensor space. -/
theorem coaction_coassociative (hA : IsPolynomialRepresentation A) (a : A) :
    actionTerm hA (coaction hA a) =
      TensorProduct.map LinearMap.id Δ (coaction hA a) := by
  apply evaluateTwo_injective
  ext ⟨g,h⟩
  rw [evaluateTwo_actionTerm, evaluateTwo_map_comultiplication Δ hΔ,
    evaluateOne_coaction]
  simp [map_mul, Module.End.mul_apply]

/-- Jantzen's regular bar differential in degree one, on actual tensors. -/
def differentialOne (hA : IsPolynomialRepresentation A) :
    CochainsOne k ι A →ₗ[k] CochainsTwo k ι A :=
  actionTerm hA - TensorProduct.map (LinearMap.id : A →ₗ[k] A) Δ +
    (appendUnit (V := A))

theorem evaluateTwo_differentialOne (hA : IsPolynomialRepresentation A)
    (t : CochainsOne k ι A) (g h : SL ι k) :
    evaluateTwo (differentialOne Δ hA t) (g,h) =
      A.ρ g (evaluateOne t h) - evaluateOne t (g*h) + evaluateOne t g := by
  simp only [differentialOne, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub,
    Pi.add_apply, Pi.sub_apply, evaluateTwo_actionTerm,
    evaluateTwo_map_comultiplication Δ hΔ, evaluateTwo_appendUnit]

theorem differentialOne_differentialZero (hA : IsPolynomialRepresentation A) (a : A) :
    differentialOne Δ hA (differentialZero hA a) = 0 := by
  apply evaluateTwo_injective
  ext ⟨g,h⟩
  rw [evaluateTwo_differentialOne Δ hΔ]
  simp [map_mul, Module.End.mul_apply]

end Comultiplication

end Guralnick.RationalCoordinate
