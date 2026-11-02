import Guralnick.SLCoordinateAntipode
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The actual Hopf algebra of determinant-one matrices

The coproduct, counit and antipode were constructed by polynomial matrix
formulas. Their Hopf laws are proved here by faithful tensor evaluation on
pairs and triples of matrices. Together with `quotientDeterminantEquiv`,
this is the usual affine-group coordinate algebra over algebraically closed
fields, with no reducedness or point-separation assumption left over.
-/
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
noncomputable section
open scoped TensorProduct
namespace Guralnick.SLCoordinate
open RationalCohomology
variable (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι]
local notation "C" => CoordinateAlgebra k ι

theorem pairEvaluation_zero : pairEvaluation k ι (0 : C ⊗[k] C) = 0 :=
  (pairEvaluation k ι).toLinearMap.map_zero

theorem pairEvaluation_add (a b : C ⊗[k] C) :
    pairEvaluation k ι (a+b) = pairEvaluation k ι a + pairEvaluation k ι b :=
  (pairEvaluation k ι).toLinearMap.map_add a b

/-- Evaluation of the genuine threefold coordinate tensor. -/
def tripleEvaluation : C ⊗[k] (C ⊗[k] C) →ₗ[k] (SL ι k × (SL ι k × SL ι k) → k) :=
  tensorEvaluation (CoordinateAlgebra k ι).val.toLinearMap (pairEvaluation k ι).toLinearMap

theorem tripleEvaluation_injective : Function.Injective (tripleEvaluation k ι) :=
  tensorEvaluation_injective _ _ Subtype.val_injective (pairEvaluation_injective k ι)

@[simp] theorem tripleEvaluation_tmul (f : C) (t : C ⊗[k] C) (g h l : SL ι k) :
    tripleEvaluation k ι (f ⊗ₜ[k] t) (g,(h,l)) = f g * pairEvaluation k ι t (h,l) := rfl

theorem tripleEvaluation_assoc_tmul (t : C ⊗[k] C) (f : C) (g h l : SL ι k) :
    tripleEvaluation k ι ((TensorProduct.assoc k C C C) (t ⊗ₜ[k] f)) (g,(h,l)) =
      pairEvaluation k ι t (g,h) * f l := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [TensorProduct.zero_tmul, (TensorProduct.assoc k C C C).map_zero,
      (tripleEvaluation k ι).map_zero, pairEvaluation_zero]
    exact (zero_mul (f l)).symm
  | add a b ha hb =>
    rw [TensorProduct.add_tmul, (TensorProduct.assoc k C C C).map_add,
      (tripleEvaluation k ι).map_add, pairEvaluation_add]
    simp only [Pi.add_apply]
    rw [ha, hb, add_mul]
  | tmul a b =>
    rw [TensorProduct.assoc_tmul, tripleEvaluation_tmul, pairEvaluation_tmul,
      pairEvaluation_tmul, mul_assoc]

theorem tripleEvaluation_left (t : C ⊗[k] C) (g h l : SL ι k) :
    tripleEvaluation k ι ((TensorProduct.assoc k C C C)
      ((comultiplication k ι).toLinearMap.rTensor C t)) (g,(h,l)) =
      pairEvaluation k ι t (g*h,l) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [((comultiplication k ι).toLinearMap.rTensor C).map_zero,
      (TensorProduct.assoc k C C C).map_zero,
      (tripleEvaluation k ι).map_zero, pairEvaluation_zero]
    rfl
  | add a b ha hb =>
    rw [((comultiplication k ι).toLinearMap.rTensor C).map_add,
      (TensorProduct.assoc k C C C).map_add,
      (tripleEvaluation k ι).map_add, pairEvaluation_add]
    exact congrArg₂ (·+·) ha hb
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, tripleEvaluation_assoc_tmul]
    change pairEvaluation k ι (comultiplication k ι a) (g,h) * b l = _
    rw [comultiplication_eval, pairEvaluation_tmul]

theorem tripleEvaluation_right (t : C ⊗[k] C) (g h l : SL ι k) :
    tripleEvaluation k ι ((comultiplication k ι).toLinearMap.lTensor C t) (g,(h,l)) =
      pairEvaluation k ι t (g,h*l) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, map_zero, TensorProduct.zero_tmul, Pi.zero_apply, zero_mul, mul_zero] <;> rfl
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, map_add, Pi.add_apply] using congrArg₂ (·+·) ha hb
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, tripleEvaluation_tmul,
      comultiplication_eval, pairEvaluation_tmul]

/-- Scalar coproduct coassociativity follows from actual matrix associativity. -/
theorem comultiplication_coassociative (f : C) :
    (TensorProduct.assoc k C C C)
      ((comultiplication k ι).toLinearMap.rTensor C (comultiplication k ι f)) =
      (comultiplication k ι).toLinearMap.lTensor C (comultiplication k ι f) := by
  apply tripleEvaluation_injective k ι
  ext ⟨g,h,l⟩
  rw [tripleEvaluation_left, tripleEvaluation_right, comultiplication_eval,
    comultiplication_eval, mul_assoc]

theorem leftCounit_evaluate (t : C ⊗[k] C) (g : SL ι k) :
    (TensorProduct.lid k C ((counit k ι).toLinearMap.rTensor C t)) g =
      pairEvaluation k ι t (1,g) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, map_zero, TensorProduct.zero_tmul, Pi.zero_apply, zero_mul, mul_zero] <;> rfl
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, map_add, Pi.add_apply] using congrArg₂ (·+·) ha hb
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    rfl

theorem rightCounit_evaluate (t : C ⊗[k] C) (g : SL ι k) :
    (TensorProduct.rid k C ((counit k ι).toLinearMap.lTensor C t)) g =
      pairEvaluation k ι t (g,1) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, map_zero, TensorProduct.zero_tmul, Pi.zero_apply, zero_mul, mul_zero] <;> rfl
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, map_add, Pi.add_apply] using congrArg₂ (·+·) ha hb
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    exact mul_comm _ _

theorem comultiplication_leftCounit (f : C) :
    (counit k ι).toLinearMap.rTensor C (comultiplication k ι f) = 1 ⊗ₜ[k] f := by
  apply (TensorProduct.lid k C).injective
  ext g
  simp only [leftCounit_evaluate, comultiplication_eval, one_mul, TensorProduct.lid_tmul, one_smul]

theorem comultiplication_rightCounit (f : C) :
    (counit k ι).toLinearMap.lTensor C (comultiplication k ι f) = f ⊗ₜ[k] 1 := by
  apply (TensorProduct.rid k C).injective
  ext g
  simp only [rightCounit_evaluate, comultiplication_eval, mul_one, TensorProduct.rid_tmul, one_smul]

instance coordinateCoalgebra : Coalgebra k C where
  comul := (comultiplication k ι).toLinearMap
  counit := (counit k ι).toLinearMap
  coassoc := by ext f; exact comultiplication_coassociative k ι f
  rTensor_counit_comp_comul := by ext f; exact comultiplication_leftCounit k ι f
  lTensor_counit_comp_comul := by ext f; exact comultiplication_rightCounit k ι f

instance coordinateBialgebra : Bialgebra k C :=
  Bialgebra.mk' k C (map_one (counit k ι)) (fun {_ _} => map_mul (counit k ι) _ _)
    (map_one (comultiplication k ι)) (fun {_ _} => map_mul (comultiplication k ι) _ _)

theorem leftAntipode_evaluate (t : C ⊗[k] C) (g : SL ι k) :
    (LinearMap.mul' k C ((antipode k ι).toLinearMap.rTensor C t)) g =
      pairEvaluation k ι t (g⁻¹,g) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, map_zero, TensorProduct.zero_tmul, Pi.zero_apply, zero_mul, mul_zero] <;> rfl
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, map_add, Pi.add_apply] using congrArg₂ (·+·) ha hb
  | tmul a b => rfl

theorem rightAntipode_evaluate (t : C ⊗[k] C) (g : SL ι k) :
    (LinearMap.mul' k C ((antipode k ι).toLinearMap.lTensor C t)) g =
      pairEvaluation k ι t (g,g⁻¹) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero, map_zero, TensorProduct.zero_tmul, Pi.zero_apply, zero_mul, mul_zero] <;> rfl
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, map_add, Pi.add_apply] using congrArg₂ (·+·) ha hb
  | tmul a b => rfl

/-- The standard matrix coordinate algebra carries an actual mathlib Hopf algebra. -/
instance coordinateHopfAlgebra : HopfAlgebra k C where
  antipode := (antipode k ι).toLinearMap
  mul_antipode_rTensor_comul := by
    ext f g
    change (LinearMap.mul' k C
      ((antipode k ι).toLinearMap.rTensor C (comultiplication k ι f))) g = _
    rw [leftAntipode_evaluate, comultiplication_eval, inv_mul_cancel]
    rfl
  mul_antipode_lTensor_comul := by
    ext f g
    change (LinearMap.mul' k C
      ((antipode k ι).toLinearMap.lTensor C (comultiplication k ι f))) g = _
    rw [rightAntipode_evaluate, comultiplication_eval, mul_inv_cancel]
    rfl

/-- Point evaluation on the standard determinant presentation of SL. -/
def standardEvaluation [IsAlgClosed k] :
    (MvPolynomial (ι × ι) k ⧸ determinantIdeal k ι) →ₐ[k] (SL ι k → k) :=
  (CoordinateAlgebra k ι).val.comp (quotientDeterminantEquiv k ι).toAlgHom

@[simp] theorem standardEvaluation_mk [IsAlgClosed k]
    (p : MvPolynomial (ι × ι) k) (g : SL ι k) :
    standardEvaluation k ι (Ideal.Quotient.mk (determinantIdeal k ι) p) g =
      polynomialEvaluation k ι p g := by
  rfl

/-- The standard coordinate algebra of SL×SL has faithful point evaluation too. -/
def standardPairEvaluation [IsAlgClosed k] :
    (MvPolynomial (ι × ι) k ⧸ determinantIdeal k ι) ⊗[k]
      (MvPolynomial (ι × ι) k ⧸ determinantIdeal k ι) →ₐ[k]
      (SL ι k × SL ι k → k) :=
  (pairEvaluation k ι).comp
    (Algebra.TensorProduct.congr (quotientDeterminantEquiv k ι)
      (quotientDeterminantEquiv k ι)).toAlgHom

theorem standardPairEvaluation_injective [IsAlgClosed k] :
    Function.Injective (standardPairEvaluation k ι) :=
  (pairEvaluation_injective k ι).comp
    (Algebra.TensorProduct.congr (quotientDeterminantEquiv k ι)
      (quotientDeterminantEquiv k ι)).injective

#print axioms coordinateHopfAlgebra
#print axioms standardPairEvaluation_injective
end Guralnick.SLCoordinate
