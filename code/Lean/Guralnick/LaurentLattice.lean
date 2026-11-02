import Mathlib.RingTheory.LaurentSeries
import Guralnick.RelativeDimensions

/-!
# Actual Laurent-series lattices

The ambient space is k((t))^N, and a lattice is an actual finitely generated
k[[t]]-submodule spanning it over k((t)). Over the discrete valuation ring
k[[t]], this is the usual full lattice definition. No arbitrary stable
k-subspace is declared to be a lattice.
-/

noncomputable section
namespace Guralnick.LaurentLattice
variable (k : Type*) [Field k] (N : ℕ)

instance scalarTower : IsScalarTower k (PowerSeries k) (LaurentSeries k) where
  smul_assoc r f x := by
    change (algebraMap (PowerSeries k) (LaurentSeries k) (r • f)) * x =
      r • ((algebraMap (PowerSeries k) (LaurentSeries k) f) * x)
    rw [PowerSeries.smul_eq_C_mul, map_mul]
    change ((HahnSeries.ofPowerSeries ℤ k) (PowerSeries.C k r)) *
      ((HahnSeries.ofPowerSeries ℤ k) f) * x = _
    rw [HahnSeries.ofPowerSeries_C]
    simp only [HahnSeries.C_apply, HahnSeries.single_zero_mul_eq_smul]
    rw [← HahnSeries.single_zero_mul_eq_smul,
      ← HahnSeries.single_zero_mul_eq_smul, mul_assoc]
    rfl

instance scalarTowerLaurent : IsScalarTower k (LaurentSeries k) (LaurentSeries k) where
  smul_assoc r x y := by
    change (r • x) * y = r • (x * y)
    simp only [← HahnSeries.single_zero_mul_eq_smul, mul_assoc]

abbrev Ambient := Fin N → LaurentSeries k

structure Lattice where
  module : Submodule (PowerSeries k) (Ambient k N)
  finite : module.FG
  spanning : Submodule.span (LaurentSeries k) (module : Set (Ambient k N)) = ⊤

namespace Lattice
variable {k N}

def space (Λ : Lattice k N) : Submodule k (Ambient k N) :=
  Λ.module.restrictScalars k

@[ext] theorem ext {Λ M : Lattice k N} (h : Λ.module = M.module) : Λ = M := by
  cases Λ; cases M; cases h; rfl

instance : PartialOrder (Lattice k N) :=
  PartialOrder.lift Lattice.module (fun _ _ h => ext h)

theorem le_space_iff {Λ M : Lattice k N} : Λ ≤ M ↔ Λ.space ≤ M.space := Iff.rfl

end Lattice

/-- Multiplication by t⁻¹ on the actual Laurent-series vector space. -/
def shift : Ambient k N ≃ₗ[k] Ambient k N :=
  (LinearEquiv.smulOfNeZero (LaurentSeries k) (Ambient k N)
    (HahnSeries.single (-1 : ℤ) (1 : k))
    (by simp)).restrictScalars k

/-- Every full lattice satisfies the periodic stability condition used by
 the elementary quotient-incidence arguments. -/
theorem stable (Λ : Lattice k N) :
    Λ.space ≤ LatticeGallery.expand (shift k N) Λ.space := by
  intro x hx
  refine ⟨(PowerSeries.X : PowerSeries k) • x, Λ.module.smul_mem _ hx, ?_⟩
  funext i
  change (HahnSeries.single (-1 : ℤ) (1 : k)) *
    ((algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) * x i) = x i
  change (HahnSeries.single (-1 : ℤ) (1 : k)) *
    ((HahnSeries.ofPowerSeries ℤ k PowerSeries.X) * x i) = x i
  rw [HahnSeries.ofPowerSeries_X, ← mul_assoc, HahnSeries.single_mul_single]
  norm_num

/-- The usual standard lattice k[[t]]^N as a submodule of k((t))^N. -/
def standardEmbedding :
    (Fin N → PowerSeries k) →ₗ[PowerSeries k] Ambient k N where
  toFun x i := algebraMap (PowerSeries k) (LaurentSeries k) (x i)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp [Algebra.smul_def]

def standardModule : Submodule (PowerSeries k) (Ambient k N) :=
  LinearMap.range (standardEmbedding k N)

/-- Signed relative degree against the actual standard lattice. Finite
relative quotients are part of the general lattice theory used separately. -/
def degree (Λ : Lattice k N) : ℤ :=
  let S := (standardModule k N).restrictScalars k
  (Module.finrank k (LatticeGallery.QuotientSpace (Λ.space ⊓ S) Λ.space) : ℤ) -
    Module.finrank k (LatticeGallery.QuotientSpace (Λ.space ⊓ S) S)

end Guralnick.LaurentLattice
