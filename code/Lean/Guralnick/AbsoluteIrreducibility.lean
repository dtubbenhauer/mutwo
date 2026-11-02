import Guralnick.Cohomology
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Absolute irreducibility and the literal all-field conjecture

Scalar extension is the actual tensor-product representation. We use the
usual definition of absolute irreducibility: irreducibility after extension
to an algebraic closure. Over an already algebraically closed field, this
follows in Lean from the algebra-map isomorphism, without an additional
representation-theoretic assumption.
-/

noncomputable section
open scoped TensorProduct
namespace Guralnick.Cohomology

variable {k G : Type} [Field k] [Group G]

/-- Extension of scalars acts on `K ⊗[k] A` by `1 ⊗ ρ(g)`. -/
def scalarExtension (K : Type) [Field K] [Algebra k K] (A : Rep k G) : Rep K G :=
  Rep.of ((Module.End.baseChangeHom k K A).toMonoidHom.comp A.ρ)

@[simp] theorem scalarExtension_tmul (K : Type) [Field K] [Algebra k K]
    (A : Rep k G) (g : G) (c : K) (x : A) :
    (scalarExtension K A).ρ g (c ⊗ₜ[k] x) = c ⊗ₜ[k] A.ρ g x := rfl

/-- The standard algebraic-closure definition of absolute irreducibility. -/
def AbsolutelyIrreducible (A : Rep k G) : Prop :=
  Irreducible (scalarExtension (AlgebraicClosure k) A)

/-- The algebraic closure of an algebraically closed field adds no scalars. -/
def closureEquiv [IsAlgClosed k] : k ≃ₐ[k] AlgebraicClosure k :=
  AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

def closureTensorEquiv [IsAlgClosed k] (A : Rep k G) :
    A ≃ₗ[k] AlgebraicClosure k ⊗[k] A :=
  (TensorProduct.lid k A).symm.trans
    (TensorProduct.congr (closureEquiv (k := k)).toLinearEquiv (LinearEquiv.refl k A))

@[simp] theorem closureTensorEquiv_apply [IsAlgClosed k] (A : Rep k G) (x : A) :
    closureTensorEquiv A x = (1 : AlgebraicClosure k) ⊗ₜ[k] x := by
  simp [closureTensorEquiv, closureEquiv]

theorem irreducible_absolutelyIrreducible [IsAlgClosed k] (A : Rep k G)
    (hA : Irreducible A) : AbsolutelyIrreducible A := by
  let e := closureTensorEquiv A
  letI : Nontrivial A := hA.1
  change Nontrivial (AlgebraicClosure k ⊗[k] A) ∧
    ∀ V : Submodule (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A),
      (∀ g : G, ∀ x : AlgebraicClosure k ⊗[k] A, x ∈ V →
        (A.ρ g).baseChange (AlgebraicClosure k) x ∈ V) → V = ⊥ ∨ V = ⊤
  refine ⟨e.injective.nontrivial, ?_⟩
  intro V hV
  let U : Submodule k A := (V.restrictScalars k).comap e.toLinearMap
  have hU : ∀ g : G, ∀ x : A, x ∈ U → A.ρ g x ∈ U := by
    intro g x hx
    change e (A.ρ g x) ∈ V
    change e x ∈ V at hx
    simpa only [e, closureTensorEquiv_apply, LinearMap.baseChange_tmul] using hV g (e x) hx
  rcases hA.2 U hU with h | h
  · left
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ∈ U := hx
    rw [h] at hy
    have hy0 : y = 0 := hy
    simp [hy0]
  · right
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ∈ U := by rw [h]; trivial
    exact hy

/-- All hypotheses on the modules in the all-field formulation. -/
def AbsolutelyAdmissible (A : Rep k G) : Prop :=
  FiniteDimensional k A ∧ Faithful A ∧ AbsolutelyIrreducible A

theorem admissible_absolutelyAdmissible [IsAlgClosed k] (A : Rep k G)
    (hA : Admissible A) : AbsolutelyAdmissible A :=
  ⟨hA.1, hA.2.1, irreducible_absolutelyIrreducible A hA.2.2⟩

/-- A single bound over all fields (with no characteristic restriction),
finite groups, and faithful finite-dimensional absolutely irreducible modules. -/
def AbsoluteUniformH1Bound (C : ℕ) : Prop :=
  ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (A : Rep k G),
    AbsolutelyAdmissible A → h1Dimension A ≤ C

def AbsoluteBoundedness : Prop := ∃ C : ℕ, AbsoluteUniformH1Bound C

theorem absoluteBound_implies_algebraicallyClosedBound {C : ℕ}
    (h : AbsoluteUniformH1Bound C) : UniformH1Bound C := by
  intro k _ _ G _ _ A hA
  exact h k G A (admissible_absolutelyAdmissible A hA)

theorem not_absoluteBoundedness_of_row_and_transfer (μ : ℕ → ℕ → ℕ)
    (hrow : DoubledRowSum μ) (htransfer : PrimeFieldTransfer μ) :
    ¬AbsoluteBoundedness := by
  rintro ⟨C, hC⟩
  exact not_algebraicallyClosedBoundedness μ hrow htransfer
    ⟨C, absoluteBound_implies_algebraicallyClosedBound hC⟩

end Guralnick.Cohomology
