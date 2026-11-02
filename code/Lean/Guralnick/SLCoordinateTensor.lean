import Guralnick.RationalCohomology
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Faithful evaluation of tensor products of function spaces

This is the linear-algebra step needed to read coordinate-algebra identities
as identities on points. It requires injectivity of the individual function
realizations and holds for arbitrary sets over a field; it does not assume
that an unevaluated polynomial is determined by finitely many field points.
-/
noncomputable section
open scoped TensorProduct

namespace Guralnick.SLCoordinate

variable {k X Y M N : Type} [Field k]
variable [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Evaluation of a tensor of scalar-valued functions on the product set. -/
def tensorEvaluation (f : M →ₗ[k] (X → k)) (g : N →ₗ[k] (Y → k)) :
    M ⊗[k] N →ₗ[k] (X × Y → k) :=
  TensorProduct.lift
    { toFun := fun m =>
        { toFun := fun n p => f m p.1 * g n p.2
          map_add' := by intros; ext p; simp [mul_add]
          map_smul' := by intros; ext p; simp [mul_left_comm] }
      map_add' := by intros; ext n p; simp [add_mul]
      map_smul' := by intros; ext n p; simp [mul_assoc] }

@[simp] theorem tensorEvaluation_tmul
    (f : M →ₗ[k] (X → k)) (g : N →ₗ[k] (Y → k)) (m : M) (n : N) (x : X) (y : Y) :
    tensorEvaluation f g (m ⊗ₜ[k] n) (x,y) = f m x * g n y := rfl

/-- Pure-point evaluations separate every tensor, not only pure tensors. -/
theorem tensorEvaluation_injective
    (f : M →ₗ[k] (X → k)) (g : N →ₗ[k] (Y → k))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (tensorEvaluation f g) := by
  classical
  apply (injective_iff_map_eq_zero _).2
  intro t ht
  let b := Module.Free.chooseBasis k M
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hli : LinearIndependent k (fun i => f (b i)) := b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hc : ∀ y : Y, c.sum (fun i n => g n y • f (b i)) = 0 := by
    intro y
    ext x
    have h := congrFun ht (x,y)
    simpa [Finsupp.sum, tensorEvaluation_tmul, mul_comm] using h
  have cz : c = 0 := by
    ext i
    apply hg
    ext y
    have hz : c.mapRange (fun n => g n y) (by simp) = 0 := by
      apply hli.finsuppLinearCombination_injective
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index] using hc y
    have hi := congrArg (fun d => d i) hz
    simpa using hi
  simp [cz]

end Guralnick.SLCoordinate
