import Guralnick.RationalCoordinateH1
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Rational actions and coordinate-algebra comodules

The comodule below is defined independently by a tensor-valued linear map,
counit and coassociativity. Evaluation constructs an actual group
representation; the polynomial-action construction is its inverse. Linear
intertwiners and invariant subspaces agree, including the tensor-image
definition of a subcomodule. These results justify using the same simple
highest-weight module in the two descriptions.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
noncomputable section
open scoped TensorProduct

namespace Guralnick.RationalCoordinate
open RationalCohomology SLCoordinate

variable {k ι V W : Type} [Field k] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

def iterateCoaction (δ : V →ₗ[k] CochainsOne k ι V) :
    CochainsOne k ι V →ₗ[k] CochainsTwo k ι V :=
  (TensorProduct.assoc k V (CoordinateAlgebra k ι) (CoordinateAlgebra k ι)).toLinearMap.comp
    (TensorProduct.map δ LinearMap.id)

omit [FiniteDimensional k V] in
theorem evaluateTwo_iterateCoaction (δ : V →ₗ[k] CochainsOne k ι V)
    (t : CochainsOne k ι V) (g h : SL ι k) :
    evaluateTwo (iterateCoaction δ t) (g,h) =
      evaluateOne (δ (evaluateOne t h)) g := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp [ht, hu]
  | tmul a f => simp [iterateCoaction, evaluateTwo_assoc_tmul]

/-- A genuine right coordinate-algebra comodule, with the tensor identities
which represent the identity and composition laws of an algebraic action. -/
structure CoordinateRepresentation (k ι V : Type) [Field k] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] where
  coact : V →ₗ[k] CochainsOne k ι V
  counit : ∀ a, evaluateOne (coact a) 1 = a
  coassociative : ∀ a,
    iterateCoaction coact (coact a) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (comultiplication k ι).toLinearMap (coact a)

namespace CoordinateRepresentation

@[ext] theorem ext {R S : CoordinateRepresentation k ι V} (h : R.coact = S.coact) : R = S := by
  cases R
  cases S
  cases h
  rfl

variable (R : CoordinateRepresentation k ι V)

/-- Evaluation of a comodule produces the actual matrix-group action. -/
def pointAction : Representation k (SL ι k) V where
  toFun g := (LinearMap.proj g).comp (evaluateOne.comp R.coact)
  map_one' := by ext a; exact R.counit a
  map_mul' g h := by
    ext a
    have he := congrArg (fun z => evaluateTwo z (g,h)) (R.coassociative a)
    dsimp only at he
    rw [evaluateTwo_iterateCoaction,
      evaluateTwo_map_comultiplication _ scalarEvaluateTwo_comultiplication] at he
    exact he.symm

abbrev pointRep : Rep k (SL ι k) := Rep.of R.pointAction

theorem pointRep_polynomial : IsPolynomialRepresentation R.pointRep := by
  intro a
  exact (cochainEquiv (R.coact a)).property

/-- The counit field is exactly the usual tensor counit equation. -/
theorem counit_tensor (a : V) :
    TensorProduct.rid k V
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (SLCoordinate.counit k ι).toLinearMap (R.coact a)) = a := by
  have he (t : CochainsOne k ι V) :
      TensorProduct.rid k V
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (SLCoordinate.counit k ι).toLinearMap t) = evaluateOne t 1 := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t u ht hu => simp [ht, hu]
    | tmul a f => simp
  rw [he, R.counit]

end CoordinateRepresentation

variable {A : Rep k (SL ι k)} [FiniteDimensional k A]

/-- Polynomial actions give actual comodules, with both axioms proved. -/
def toCoordinateRepresentation (hA : IsPolynomialRepresentation A) :
    CoordinateRepresentation k ι A where
  coact := coaction hA
  counit := coaction_counit hA
  coassociative := coaction_coassociative _ scalarEvaluateTwo_comultiplication hA

@[simp] theorem toCoordinateRepresentation_pointAction (hA : IsPolynomialRepresentation A) :
    (toCoordinateRepresentation hA).pointAction = A.ρ := by
  ext g a
  exact congrFun (evaluateOne_coaction hA a) g

@[simp] theorem toCoordinateRepresentation_pointRep (hA : IsPolynomialRepresentation A) :
    (toCoordinateRepresentation hA).pointRep = A := by
  change Rep.of (toCoordinateRepresentation hA).pointAction = A
  rw [toCoordinateRepresentation_pointAction]
  rfl

/-- The reconstruction recovers the original tensor map, not merely an
isomorphic vector space or a matching dimension. -/
theorem coordinateRepresentation_roundtrip (R : CoordinateRepresentation k ι V) :
    (toCoordinateRepresentation R.pointRep_polynomial).coact = R.coact := by
  ext a
  apply evaluateOne_injective
  change evaluateOne (coaction R.pointRep_polynomial a) = _
  rw [evaluateOne_coaction]
  rfl

theorem coordinateRepresentation_roundtrip_full (R : CoordinateRepresentation k ι V) :
    toCoordinateRepresentation R.pointRep_polynomial = R :=
  CoordinateRepresentation.ext (coordinateRepresentation_roundtrip R)

omit [FiniteDimensional k V] [FiniteDimensional k W] in
theorem evaluateOne_map_target (L : V →ₗ[k] W) (t : CochainsOne k ι V) (g : SL ι k) :
    evaluateOne (TensorProduct.map L LinearMap.id t) g = L (evaluateOne t g) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp [ht, hu]
  | tmul a f => simp

/-- Intertwining the point actions is exactly intertwining their coactions. -/
theorem intertwiner_iff (R : CoordinateRepresentation k ι V)
    (S : CoordinateRepresentation k ι W) (L : V →ₗ[k] W) :
    (∀ g a, L (R.pointAction g a) = S.pointAction g (L a)) ↔
      TensorProduct.map L LinearMap.id ∘ₗ R.coact = S.coact ∘ₗ L := by
  constructor
  · intro h
    ext a
    apply evaluateOne_injective
    ext g
    exact (evaluateOne_map_target L (R.coact a) g).trans (h g a)
  · intro h g a
    have he := congrArg (fun f => evaluateOne (f a) g) h
    simpa only [LinearMap.comp_apply, evaluateOne_map_target] using he

/-- The tensor-image subcomodule condition is exactly pointwise invariance.
Right exactness of the actual tensor product, not an assumption about
dimensions, identifies that image with the kernel after quotienting. -/
theorem invariant_subspace_iff (hA : IsPolynomialRepresentation A) (U : Submodule k A) :
    (∀ g a, a ∈ U → A.ρ g a ∈ U) ↔
      ∀ a, a ∈ U → coaction hA a ∈
        LinearMap.range (U.subtype.rTensor (CoordinateAlgebra k ι)) := by
  have hker := rTensor_mkQ (CoordinateAlgebra k ι) U
  constructor
  · intro h a ha
    rw [← hker, LinearMap.mem_ker]
    apply evaluateOne_injective
    ext g
    change evaluateOne (TensorProduct.map U.mkQ LinearMap.id (coaction hA a)) g = 0
    rw [evaluateOne_map_target, evaluateOne_coaction]
    exact Submodule.Quotient.mk_eq_zero U |>.mpr (h g a ha)
  · intro h g a ha
    have he := h a ha
    rw [← hker, LinearMap.mem_ker] at he
    have hh := congrArg (fun z => evaluateOne z g) he
    change evaluateOne (TensorProduct.map U.mkQ LinearMap.id (coaction hA a)) g = 0 at hh
    rw [evaluateOne_map_target, evaluateOne_coaction] at hh
    exact Submodule.Quotient.mk_eq_zero U |>.mp hh

end Guralnick.RationalCoordinate
