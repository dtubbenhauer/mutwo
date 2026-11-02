import Guralnick.LaurentLattice
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Subspaces in a one-period interval are actual lattices

A k-subspace A between a full k[[t]] lattice Λ and t⁻¹Λ is stable under
power-series multiplication: split a power series as its constant term
plus t times another power series. Multiplication by t embeds the resulting
k[[t]] module in Λ, so Noetherianity gives finite generation. Containment
of Λ supplies fullness. No lattice-realization input is used here.
-/
noncomputable section
namespace Guralnick.LaurentLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- Multiplication by t cancels the actual Laurent-series shift. -/
theorem X_smul_shift (x : Ambient k N) :
    (PowerSeries.X : PowerSeries k) • (shift k N x) = x := by
  funext i
  change (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) *
    ((HahnSeries.single (-1 : ℤ) (1 : k)) * x i) = x i
  change (HahnSeries.ofPowerSeries ℤ k PowerSeries.X) *
    ((HahnSeries.single (-1 : ℤ) (1 : k)) * x i) = x i
  rw [HahnSeries.ofPowerSeries_X, ← mul_assoc, HahnSeries.single_mul_single]
  norm_num

/-- The inverse cancellation in the other order. -/
theorem shift_X_smul (x : Ambient k N) :
    shift k N ((PowerSeries.X : PowerSeries k) • x) = x := by
  funext i
  change (HahnSeries.single (-1 : ℤ) (1 : k)) *
    ((algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) * x i) = x i
  change (HahnSeries.single (-1 : ℤ) (1 : k)) *
    ((HahnSeries.ofPowerSeries ℤ k PowerSeries.X) * x i) = x i
  rw [HahnSeries.ofPowerSeries_X, ← mul_assoc, HahnSeries.single_mul_single]
  norm_num

/-- Multiplication by t is injective, including in ambient dimension zero. -/
theorem X_smul_injective :
    Function.Injective (fun x : Ambient k N => (PowerSeries.X : PowerSeries k) • x) := by
  intro x y h
  simpa only [shift_X_smul] using congrArg (shift k N) h

/-- A constant power series acts by the original k-vector-space action. -/
theorem C_smul_eq (a : k) (x : Ambient k N) :
    PowerSeries.C k a • x = a • x := by
  funext i
  change (HahnSeries.ofPowerSeries ℤ k (PowerSeries.C k a)) * x i = a • x i
  rw [HahnSeries.ofPowerSeries_C]
  exact HahnSeries.single_zero_mul_eq_smul

/-- The upper bound in the interval makes tA a submodule of Λ. -/
theorem X_smul_mem_of_le_expand (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space)
    {x : Ambient k N} (hx : x ∈ A) :
    (PowerSeries.X : PowerSeries k) • x ∈ Λ.module := by
  obtain ⟨y, hy, rfl⟩ := hupper hx
  change (PowerSeries.X : PowerSeries k) • (shift k N y) ∈ Λ.module
  rw [X_smul_shift]
  exact hy

/-- Every intermediate k-subspace is stable under all power series. -/
theorem interval_smul_mem (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space)
    (f : PowerSeries k) {x : Ambient k N} (hx : x ∈ A) : f • x ∈ A := by
  rw [PowerSeries.eq_shift_mul_X_add_const f, add_smul, mul_smul, C_smul_eq]
  exact A.add_mem
    (hlower (Λ.module.smul_mem _ (X_smul_mem_of_le_expand Λ A hupper hx)))
    (A.smul_mem _ hx)

/-- The actual k[[t]] submodule with underlying k-subspace A. -/
def intervalModule (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    Submodule (PowerSeries k) (Ambient k N) where
  carrier := A
  zero_mem' := A.zero_mem
  add_mem' := A.add_mem
  smul_mem' := interval_smul_mem Λ A hlower hupper

/-- Multiplication by t realizes the intermediate module as a submodule
of the original lattice; this is the finite-generation mechanism. -/
def intervalIntoSource (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    intervalModule Λ A hlower hupper →ₗ[PowerSeries k] Λ.module where
  toFun x := ⟨(PowerSeries.X : PowerSeries k) • x.val,
    X_smul_mem_of_le_expand Λ A hupper x.property⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' a x := by
    apply Subtype.ext
    exact smul_comm (PowerSeries.X : PowerSeries k) a x.val

/-- The module injection does not need a choice of basis or coordinates. -/
theorem intervalIntoSource_injective (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    Function.Injective (intervalIntoSource Λ A hlower hupper) := by
  intro x y h
  apply Subtype.ext
  exact X_smul_injective (congrArg Subtype.val h)

/-- Noetherianity of k[[t]] makes the intermediate module finitely generated. -/
theorem intervalModule_finite (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    (intervalModule Λ A hlower hupper).FG := by
  letI : IsNoetherian (PowerSeries k) Λ.module :=
    isNoetherian_of_fg_of_noetherian Λ.module Λ.finite
  letI : Module.Finite (PowerSeries k) (intervalModule Λ A hlower hupper) :=
    Module.Finite.of_injective (intervalIntoSource Λ A hlower hupper)
      (intervalIntoSource_injective Λ A hlower hupper)
  exact Module.Finite.iff_fg.mp inferInstance

/-- The intermediate module spans the Laurent-series vector space because
it contains Λ. -/
theorem intervalModule_spanning (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    Submodule.span (LaurentSeries k)
      (intervalModule Λ A hlower hupper : Set (Ambient k N)) = ⊤ := by
  apply top_unique
  rw [← Λ.spanning]
  exact Submodule.span_mono hlower

/-- Uniform construction of an actual full lattice from a subspace in the
one-period interval. -/
def intervalLattice (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) : Lattice k N where
  module := intervalModule Λ A hlower hupper
  finite := intervalModule_finite Λ A hlower hupper
  spanning := intervalModule_spanning Λ A hlower hupper

@[simp] theorem intervalLattice_space (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    (intervalLattice Λ A hlower hupper).space = A := rfl

/-- The one-period lattice lift is proved from the actual lattice definition,
not supplied as an external literature assumption. -/
theorem interval_lift (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    ∃ M : Lattice k N, M.space = A :=
  ⟨intervalLattice Λ A hlower hupper, rfl⟩

/-- At the lower endpoint the construction returns the original actual lattice. -/
@[simp] theorem intervalLattice_source_eq (Λ : Lattice k N) :
    intervalLattice Λ Λ.space le_rfl (stable k N Λ) = Λ := by
  apply Lattice.ext
  ext x
  rfl

/-- At the upper endpoint the constructed module is exactly the image of
Λ under the k[[t]]-linear Laurent shift, with its full winding information. -/
theorem intervalLattice_upper_module (Λ : Lattice k N) :
    (intervalLattice Λ (LatticeGallery.expand (shift k N) Λ.space)
      (stable k N Λ) le_rfl).module =
      Λ.module.map
        (((LinearEquiv.smulOfNeZero (LaurentSeries k) (Ambient k N)
          (HahnSeries.single (-1 : ℤ) (1 : k)) (by simp)).restrictScalars
            (PowerSeries k)).toLinearMap) := by
  ext x
  rfl

#print axioms interval_lift
#print axioms intervalLattice_source_eq
#print axioms intervalLattice_upper_module
end Guralnick.LaurentLattice
