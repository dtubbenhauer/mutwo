import Guralnick.SLCoordinateTensor
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Vector-valued coordinate functions

This file proves the finite-dimensional tensor/function comparison, independently
of any group or cohomology.  The tensor product is the genuine module tensor
product; its evaluation is injective because scalar coordinate functions are
actual functions.  The inverse on coordinatewise regular functions is written
using a basis and proved inverse, rather than postulated.
-/

noncomputable section
open scoped TensorProduct BigOperators

namespace Guralnick.CoordinateTensor

variable {k G V : Type} [Field k] [AddCommGroup V] [Module k V]

variable {D : Type} [AddCommGroup D] [Module k D]

/-- Evaluation with respect to any scalar coordinate realization. -/
def linearEvaluation (e : D →ₗ[k] (G → k)) : V ⊗[k] D →ₗ[k] (G → V) :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun f g => e f g • a
          map_add' := by intros; ext; simp [add_smul]
          map_smul' := by intros; ext; simp [smul_smul] }
      map_add' := by intros; ext; simp [smul_add]
      map_smul' := by intros; ext; simp [smul_smul, mul_comm] }

@[simp] theorem linearEvaluation_tmul (e : D →ₗ[k] (G → k))
    (a : V) (f : D) (g : G) :
    linearEvaluation e (a ⊗ₜ[k] f) g = e f g • a := rfl

theorem linearEvaluation_injective (e : D →ₗ[k] (G → k))
    (he : Function.Injective e) {I : Type} [Fintype I] (b : Basis I k V) :
    Function.Injective (linearEvaluation (V := V) e) := by
  let c : V →ₗ[k] (I → k) := b.equivFun.toLinearMap
  have hc : Function.Injective c := b.equivFun.injective
  have hcompat (t : V ⊗[k] D) :
      SLCoordinate.tensorEvaluation c e t = fun p => b.coord p.1 (linearEvaluation e t p.2) := by
    induction t using TensorProduct.induction_on with
    | zero => ext p; simp
    | add t u ht hu => ext p; simp [ht, hu]
    | tmul a f => ext ⟨i, g⟩; simp [c, mul_comm]
  intro t u h
  apply SLCoordinate.tensorEvaluation_injective c e hc he
  rw [hcompat, hcompat, h]

/-- Evaluation of vector-valued coordinate tensors. -/
def evaluation (C : Submodule k (G → k)) : V ⊗[k] C →ₗ[k] (G → V) :=
  linearEvaluation C.subtype

@[simp] theorem evaluation_tmul (C : Submodule k (G → k)) (a : V) (f : C) (g : G) :
    evaluation C (a ⊗ₜ[k] f) g = f.val g • a := rfl

/-- Coordinatewise membership in the scalar coordinate space. -/
def regular (C : Submodule k (G → k)) {I : Type} [Fintype I] (b : Basis I k V) :
    Submodule k (G → V) where
  carrier := {f | ∀ i, (fun g => b.coord i (f g)) ∈ C}
  zero_mem' := by
    intro i
    simp only [Pi.zero_apply, map_zero]
    exact C.zero_mem
  add_mem' := by
    intro f h hf hh i
    simpa using C.add_mem (hf i) (hh i)
  smul_mem' := by
    intro a f hf i
    simpa using C.smul_mem a (hf i)

variable (C : Submodule k (G → k)) {I : Type} [Fintype I] (b : Basis I k V)

theorem evaluation_mem_regular (t : V ⊗[k] C) : evaluation C t ∈ regular C b := by
  induction t using TensorProduct.induction_on with
  | zero => exact (regular C b).zero_mem
  | add t u ht hu => simpa only [map_add] using (regular C b).add_mem ht hu
  | tmul a f =>
    intro i
    have h := C.smul_mem (b.coord i a) f.property
    simp only [evaluation_tmul, map_smul]
    convert h using 1
    ext g
    simp [mul_comm]

def coordinate (i : I) : regular C b →ₗ[k] C where
  toFun f := ⟨fun g => b.coord i (f.val g), f.property i⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The elementary tensor reconstruction from the scalar coordinate functions. -/
def reconstruction : regular C b →ₗ[k] V ⊗[k] C :=
  ∑ i, (TensorProduct.mk k V C (b i)).comp (coordinate C b i)

@[simp] theorem reconstruction_apply (f : regular C b) :
    reconstruction C b f =
      ∑ i, b i ⊗ₜ[k] (⟨fun g => b.coord i (f.val g), f.property i⟩ : C) := by
  simp [reconstruction, coordinate]

theorem evaluation_reconstruction (f : regular C b) :
    evaluation C (reconstruction C b f) = f.val := by
  ext g
  simp only [reconstruction_apply, map_sum,
    Finset.sum_apply, evaluation_tmul]
  exact b.sum_repr (f.val g)

theorem reconstruction_evaluation (t : V ⊗[k] C) :
    reconstruction C b ⟨evaluation C t, evaluation_mem_regular C b t⟩ = t := by
  induction t using TensorProduct.induction_on with
  | zero =>
    change reconstruction C b 0 = 0
    exact map_zero _
  | add t u ht hu =>
    simp only [map_add]
    change reconstruction C b
      (⟨evaluation C t, evaluation_mem_regular C b t⟩ +
       ⟨evaluation C u, evaluation_mem_regular C b u⟩) = t + u
    rw [map_add, ht, hu]
  | tmul a f =>
    rw [reconstruction_apply]
    change (∑ i, b i ⊗ₜ[k]
      (⟨fun g => b.coord i (f.val g • a), _⟩ : C)) = a ⊗ₜ[k] f
    have hc (i : I) : (⟨fun g => b.coord i (f.val g • a),
        (evaluation_mem_regular C b (a ⊗ₜ[k] f)) i⟩ : C) =
        (b.coord i a) • f := by ext g; simp [mul_comm]
    simp_rw [hc, TensorProduct.tmul_smul]
    calc
      _ = (∑ i, b.coord i a • b i) ⊗ₜ[k] f := by
        rw [TensorProduct.sum_tmul]
        apply Finset.sum_congr rfl
        intro i hi
        exact TensorProduct.smul_tmul' _ _ _
      _ = a ⊗ₜ[k] f := by
        change (∑ i, b.repr a i • b i) ⊗ₜ[k] f = _
        rw [b.sum_repr]

/-- Tensor coordinates and actual coordinatewise regular functions agree. -/
def regularEquiv : V ⊗[k] C ≃ₗ[k] regular C b where
  toFun t := ⟨evaluation C t, evaluation_mem_regular C b t⟩
  invFun := reconstruction C b
  left_inv := reconstruction_evaluation C b
  right_inv f := Subtype.ext (evaluation_reconstruction C b f)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem evaluation_injective (b : Basis I k V) :
    Function.Injective (evaluation (V := V) C) := by
  intro t u h
  apply (regularEquiv C b).injective
  exact Subtype.ext h

end Guralnick.CoordinateTensor
