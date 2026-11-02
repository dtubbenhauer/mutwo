import Guralnick.LatticeCompletionCoordinates

/-! Actual intersections and sums in the polynomial lattice model, and their
natural completed counterparts. -/
noncomputable section
namespace Guralnick.PolynomialLattice
variable {k : Type} [Field k] {N : ℕ}

def interLattice (Λ M : Lattice k N) : Lattice k N where
  module := Λ.module ⊓ M.module
  finite := by
    letI : IsNoetherian (Polynomial k) Λ.module :=
      isNoetherian_of_fg_of_noetherian _ Λ.finite
    let f : ↥(Λ.module ⊓ M.module) →ₗ[Polynomial k] Λ.module := Submodule.inclusion inf_le_left
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : Λ.module => z.val) h)
    letI : Module.Finite (Polynomial k) ↥(Λ.module ⊓ M.module) := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.mp inferInstance
  spanning := by
    apply top_unique
    intro x hx
    obtain ⟨r,hr⟩ := exists_X_pow_smul_mem k N Λ x
    obtain ⟨s,hs⟩ := exists_X_pow_smul_mem k N M x
    have hm : (Polynomial.X : Polynomial k)^(max r s) • x ∈ Λ.module ⊓ M.module :=
      ⟨X_pow_smul_mem_of_le k N Λ (le_max_left r s) hr,
        X_pow_smul_mem_of_le k N M (le_max_right r s) hs⟩
    have h := (Submodule.span (LaurentPolynomial k)
      (Λ.module ⊓ M.module : Set (Ambient k N))).smul_mem
        (LaurentPolynomial.T (-((max r s : ℕ) : ℤ))) (Submodule.subset_span hm)
    convert h using 1
    funext i
    change x i = LaurentPolynomial.T (-((max r s : ℕ) : ℤ)) *
      (Polynomial.toLaurent (Polynomial.X^(max r s)) * x i)
    rw [Polynomial.toLaurent_X_pow,← mul_assoc,← LaurentPolynomial.T_add,
      neg_add_cancel,LaurentPolynomial.T_zero,one_mul]

def sumLattice (Λ M : Lattice k N) : Lattice k N where
  module := Λ.module ⊔ M.module
  finite := Λ.finite.sup M.finite
  spanning := by
    apply top_unique
    rw [← Λ.spanning]
    exact Submodule.span_mono (show Λ.module ≤ Λ.module ⊔ M.module from le_sup_left)

@[simp] theorem interLattice_space (Λ M : Lattice k N) :
    (interLattice Λ M).space = Λ.space ⊓ M.space := rfl

@[simp] theorem sumLattice_space (Λ M : Lattice k N) :
    (sumLattice Λ M).space = Λ.space ⊔ M.space := by
  ext x
  change x ∈ Λ.module ⊔ M.module ↔ x ∈ Λ.space ⊔ M.space
  simp only [Submodule.mem_sup]
  rfl

end Guralnick.PolynomialLattice

namespace Guralnick.LatticeCompletion
variable {k : Type} [Field k] {N : ℕ}

theorem complete_inter (Λ M : PolynomialLattice.Lattice k N) :
    complete (PolynomialLattice.interLattice Λ M) =
      LaurentLattice.interLattice (complete Λ) (complete M) := by
  apply orderIso.symm.injective
  apply PolynomialLattice.Lattice.ext
  ext x
  change x ∈ (algebraize (complete (PolynomialLattice.interLattice Λ M))).module ↔
    (PolynomialLattice.vectorInclusion k N x ∈ (complete Λ).module ∧
      PolynomialLattice.vectorInclusion k N x ∈ (complete M).module)
  rw [algebraize_complete]
  exact ((complete_mem_iff Λ x).and (complete_mem_iff M x)).symm

theorem complete_sum_module (Λ M : PolynomialLattice.Lattice k N) :
    (complete (PolynomialLattice.sumLattice Λ M)).module =
      (complete Λ).module ⊔ (complete M).module := by
  apply le_antisymm
  · apply (complete_le_iff _ _).mpr
    apply sup_le
    · intro x hx
      exact (show (complete Λ).module ≤ (complete Λ).module ⊔ (complete M).module from le_sup_left)
        (mem_completeModule hx)
    · intro x hx
      exact (show (complete M).module ≤ (complete Λ).module ⊔ (complete M).module from le_sup_right)
        (mem_completeModule hx)
  · exact sup_le (completeModule_mono le_sup_left) (completeModule_mono le_sup_right)

theorem complete_inter_space (Λ M : PolynomialLattice.Lattice k N) :
    (complete (PolynomialLattice.interLattice Λ M)).space =
      (complete Λ).space ⊓ (complete M).space := by
  rw [complete_inter,LaurentLattice.interLattice_space]

theorem complete_sum_space (Λ M : PolynomialLattice.Lattice k N) :
    (complete (PolynomialLattice.sumLattice Λ M)).space =
      (complete Λ).space ⊔ (complete M).space := by
  change ((complete (PolynomialLattice.sumLattice Λ M)).module).restrictScalars k = _
  rw [complete_sum_module]
  ext x
  change x ∈ (complete Λ).module ⊔ (complete M).module ↔
    x ∈ (complete Λ).space ⊔ (complete M).space
  simp only [Submodule.mem_sup]
  rfl

end Guralnick.LatticeCompletion
