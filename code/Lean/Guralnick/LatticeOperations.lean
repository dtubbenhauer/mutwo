import Guralnick.LatticeQuotientFinite
import Mathlib.LinearAlgebra.StdBasis

/-!
# The standard lattice and intersections

These constructions use actual finitely generated power-series submodules.
Their full Laurent span is proved, not included as a lattice-theory premise.
-/
noncomputable section
namespace Guralnick.LaurentLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- The standard coordinate module is finitely generated over k[[t]]. -/
theorem standardModule_finite : (standardModule k N).FG := by
  unfold standardModule
  exact Module.Finite.iff_fg.mp inferInstance

/-- The coordinate vectors in the standard module span the actual ambient
Laurent-series vector space. -/
theorem standardModule_spanning :
    Submodule.span (LaurentSeries k) (standardModule k N : Set (Ambient k N)) = ⊤ := by
  classical
  apply top_unique
  rw [← (Pi.basisFun (LaurentSeries k) (Fin N)).span_eq]
  apply Submodule.span_mono
  rintro x ⟨i,rfl⟩
  refine ⟨Pi.single i 1,?_⟩
  ext j
  simp [standardEmbedding,Pi.basisFun_apply,Pi.single_apply]

/-- The actual standard full lattice k[[t]]^N. -/
def standardLattice (k : Type*) [Field k] (N : ℕ) : Lattice k N where
  module := standardModule k N
  finite := standardModule_finite
  spanning := standardModule_spanning

@[simp] theorem standardLattice_space :
    (standardLattice k N).space = (standardModule k N).restrictScalars k := rfl

/-- Intersections remain finitely generated, by Noetherianity and their
inclusion in one of the two given lattices. -/
theorem interModule_finite (Λ M : Lattice k N) : (Λ.module ⊓ M.module).FG := by
  letI : IsNoetherian (PowerSeries k) Λ.module :=
    isNoetherian_of_fg_of_noetherian Λ.module Λ.finite
  let f : ↥(Λ.module ⊓ M.module) →ₗ[PowerSeries k] Λ.module :=
    Submodule.inclusion inf_le_left
  have hf : Function.Injective f := by
    intro x y h
    have hv := congrArg (fun z : Λ.module => z.val) h
    exact Subtype.ext hv
  letI : Module.Finite (PowerSeries k) ↥(Λ.module ⊓ M.module) :=
    Module.Finite.of_injective f hf
  exact Module.Finite.iff_fg.mp inferInstance

/-- Every ambient vector has a nonzero scalar multiple in both lattices;
therefore their actual intersection still has full Laurent span. -/
theorem interModule_spanning (Λ M : Lattice k N) :
    Submodule.span (LaurentSeries k)
      (Λ.module ⊓ M.module : Set (Ambient k N)) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨r,hr⟩ := exists_X_pow_smul_mem Λ x
  obtain ⟨s,hs⟩ := exists_X_pow_smul_mem M x
  let a : PowerSeries k := PowerSeries.X^(max r s)
  have hmem : a • x ∈ Λ.module ⊓ M.module :=
    ⟨X_pow_smul_mem_of_le Λ (le_max_left r s) hr,
      X_pow_smul_mem_of_le M (le_max_right r s) hs⟩
  have hspan : a • x ∈ Submodule.span (LaurentSeries k)
      (Λ.module ⊓ M.module : Set (Ambient k N)) := Submodule.subset_span hmem
  have ha : algebraMap (PowerSeries k) (LaurentSeries k) a ≠ 0 := by
    intro hh
    have hz : a = 0 := IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
      (by simpa using hh)
    exact (pow_ne_zero _ PowerSeries.X_ne_zero) hz
  have h := (Submodule.span (LaurentSeries k)
    (Λ.module ⊓ M.module : Set (Ambient k N))).smul_mem
      (algebraMap (PowerSeries k) (LaurentSeries k) a)⁻¹ hspan
  have he : (algebraMap (PowerSeries k) (LaurentSeries k) a)⁻¹ • (a • x) = x := by
    rw [← IsScalarTower.algebraMap_smul (LaurentSeries k) a x,smul_smul,inv_mul_cancel₀ ha,one_smul]
  rwa [he] at h

/-- The actual full lattice obtained by intersecting two actual lattices. -/
def interLattice (Λ M : Lattice k N) : Lattice k N where
  module := Λ.module ⊓ M.module
  finite := interModule_finite Λ M
  spanning := interModule_spanning Λ M

@[simp] theorem interLattice_space (Λ M : Lattice k N) :
    (interLattice Λ M).space = Λ.space ⊓ M.space := rfl

theorem interLattice_le_left (Λ M : Lattice k N) : interLattice Λ M ≤ Λ := by
  change Λ.module ⊓ M.module ≤ Λ.module
  exact inf_le_left
theorem interLattice_le_right (Λ M : Lattice k N) : interLattice Λ M ≤ M := by
  change Λ.module ⊓ M.module ≤ M.module
  exact inf_le_right

end Guralnick.LaurentLattice
