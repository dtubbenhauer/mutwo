import Guralnick.SphericalMaps
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integral merges from the absorption identity

If `C_P C_L = d C_P` and multiplication by `d` is injective, every relation
among the generators `C_L h` is also a relation among `C_P h`. The desired
merge is therefore an actual quotient-induced linear map. Its existence
does not require a separate Schur-theoretic assumption.
-/
noncomputable section
namespace Guralnick.SphericalMaps
variable {A : Type*} [Ring A] [Algebra R A]

def generatorMap (C : A) : A →ₗ[R] spherical C where
  toFun := generator C
  map_add' x y := Subtype.ext (mul_add C x y)
  map_smul' a x := Subtype.ext (mul_smul_comm a C x)

theorem generatorMap_surjective (C : A) : Function.Surjective (generatorMap C) := by
  rintro ⟨x,hx⟩
  obtain ⟨h,rfl⟩ := hx
  exact ⟨h,rfl⟩

/-- A cancellation argument proves the actual kernel inclusion needed to
descend from generators. No division by `d` occurs in the construction. -/
theorem generatorMap_ker_le {C_L C_P : A} {d : R}
    (hc : ∀ x : A, d • x = 0 → x = 0)
    (ha : C_P * C_L = d • C_P) :
    LinearMap.ker (generatorMap C_L) ≤ LinearMap.ker (generatorMap C_P) := by
  intro x hx
  apply Subtype.ext
  apply hc
  have hx' : C_L * x = 0 := congrArg Subtype.val hx
  change d • (C_P * x) = 0
  rw [← smul_mul_assoc,← ha,mul_assoc,hx',mul_zero]

def mergeOfAbsorption {C_L C_P : A} {d : R}
    (hc : ∀ x : A, d • x = 0 → x = 0)
    (ha : C_P * C_L = d • C_P) : Merge C_L C_P where
  linear := ((LinearMap.ker (generatorMap C_L)).liftQ (generatorMap C_P)
    (generatorMap_ker_le hc ha)).comp
      ((generatorMap C_L).quotKerEquivOfSurjective
        (generatorMap_surjective C_L)).symm.toLinearMap
  on_generator h := by
    have he : ((generatorMap C_L).quotKerEquivOfSurjective
        (generatorMap_surjective C_L)).symm (generator C_L h) =
        Submodule.Quotient.mk h := by
      apply ((generatorMap C_L).quotKerEquivOfSurjective
        (generatorMap_surjective C_L)).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    change ((LinearMap.ker (generatorMap C_L)).liftQ (generatorMap C_P)
      (generatorMap_ker_le hc ha)
      (((generatorMap C_L).quotKerEquivOfSurjective
        (generatorMap_surjective C_L)).symm (generator C_L h))).val = _
    rw [he]
    rfl

#print axioms mergeOfAbsorption
end Guralnick.SphericalMaps
