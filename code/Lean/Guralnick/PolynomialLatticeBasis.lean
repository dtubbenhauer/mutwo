import Guralnick.PolynomialLattice
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module

/-!
# The basis condition in the cited polynomial-lattice definition

Lusztig's polynomial lattice has a k[t]-basis which is also a basis of the
Laurent ambient module. The finite-generation/full-span definition in
`PolynomialLattice` is proved to supply exactly such a basis.
-/
noncomputable section
namespace Guralnick.PolynomialLattice
variable {k : Type*} [Field k] {N : ℕ}

def latticeBasisData (Λ : Lattice k N) :
    Σ r : ℕ, Basis (Fin r) (Polynomial k) Λ.module := by
  letI : Module.Finite (Polynomial k) Λ.module := Module.Finite.iff_fg.mpr Λ.finite
  letI : NoZeroSMulDivisors (Polynomial k) (Ambient k N) := {
    eq_zero_or_eq_zero_of_smul_eq_zero := by
      intro a x h
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        funext i
        have hi := congrFun h i
        change Polynomial.toLaurent a * x i = 0 at hi
        apply (mul_eq_zero.mp hi).resolve_left
        intro ha0
        exact ha (Polynomial.toLaurent_injective (by simpa using ha0)) }
  exact Module.basisOfFiniteTypeTorsionFree'

theorem latticeBasis_span {r : ℕ} (Λ : Lattice k N)
    (b : Basis (Fin r) (Polynomial k) Λ.module) :
    Submodule.span (LaurentPolynomial k) (Set.range fun i => (b i).val) = ⊤ := by
  have hs : Submodule.span (Polynomial k) (Set.range fun i => (b i).val) = Λ.module := by
    rw [show (Set.range fun i => (b i).val) = Λ.module.subtype '' Set.range b from
      Set.range_comp _ _, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  rw [← Submodule.span_span_of_tower (Polynomial k), hs]
  exact Λ.spanning

theorem latticeBasis_independent {r : ℕ} (Λ : Lattice k N)
    (b : Basis (Fin r) (Polynomial k) Λ.module) :
    LinearIndependent (LaurentPolynomial k) (fun i => (b i).val) := by
  have h := b.linearIndependent.map' Λ.module.subtype (Submodule.ker_subtype _)
  exact h.localization (LaurentPolynomial k) (Submonoid.powers (Polynomial.X : Polynomial k))

/-- The same literal vectors form a basis over Laurent-polynomial scalars. -/
def extendedBasis {r : ℕ} (Λ : Lattice k N)
    (b : Basis (Fin r) (Polynomial k) Λ.module) :
    Basis (Fin r) (LaurentPolynomial k) (Ambient k N) :=
  Basis.mk (latticeBasis_independent Λ b) (le_of_eq (latticeBasis_span Λ b).symm)

theorem latticeBasis_card {r : ℕ} (Λ : Lattice k N)
    (b : Basis (Fin r) (Polynomial k) Λ.module) : r = N := by
  have h := Module.finrank_eq_card_basis (extendedBasis Λ b)
  simpa using h.symm

def latticeBasis (Λ : Lattice k N) : Basis (Fin N) (Polynomial k) Λ.module :=
  (latticeBasisData Λ).2.reindex (finCongr (latticeBasis_card Λ (latticeBasisData Λ).2))

/-- The basis exists with the ambient rank and its actual scalar extension. -/
theorem exists_basis_extending (Λ : Lattice k N) :
    ∃ b : Basis (Fin N) (Polynomial k) Λ.module,
      ∃ B : Basis (Fin N) (LaurentPolynomial k) (Ambient k N), ∀ i, B i = (b i).val := by
  refine ⟨latticeBasis Λ, extendedBasis Λ (latticeBasis Λ), ?_⟩
  intro i
  simp [extendedBasis]

end Guralnick.PolynomialLattice
