import Guralnick.LatticeDegree

/-!
# Proved general facts of the actual lattice realization

These general full-lattice facts over k[[t]] are used in the affine flag
realization of Schur convolution. Their bundle is constructed below from
the proved basis, denominator-clearing, quotient and signed-degree lemmas.
It is no longer an external literature input. No special six-map gallery,
matrix support, count polynomial or canonical correction is assumed here.
-/
noncomputable section
namespace Guralnick.LaurentLattice
variable (k : Type*) [Field k] (N : ℕ)

/-- A convenient bundle of general lattice facts, all proved below. -/
structure Theory : Prop where
  finite_quotient : ∀ Λ M : Lattice k N, Λ ≤ M →
    FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space M.space)
  dimension_degree : ∀ Λ M : Lattice k N, Λ ≤ M →
    (Module.finrank k (LatticeGallery.QuotientSpace Λ.space M.space) : ℤ) =
      degree k N M - degree k N Λ
  period_dimension : ∀ Λ : Lattice k N,
    Module.finrank k (LatticeGallery.QuotientSpace Λ.space
      (LatticeGallery.expand (shift k N) Λ.space)) = N
  period_finite : ∀ Λ : Lattice k N,
    FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space
      (LatticeGallery.expand (shift k N) Λ.space))

/-- The entire lattice-theory bundle follows from the actual lattice
definition and mathlib. No literature interface is a hypothesis. -/
theorem provedTheory : Theory k N where
  finite_quotient := LaurentLattice.finite_quotient
  dimension_degree := LaurentLattice.dimension_degree
  period_dimension := LaurentLattice.period_dimension
  period_finite := LaurentLattice.period_finite

namespace Lattice
variable {k N}

theorem space_injective : Function.Injective (space : Lattice k N → _) := by
  intro Λ M h
  apply Lattice.ext
  ext x
  change x ∈ Λ.space ↔ x ∈ M.space
  rw [h]

end Lattice

variable {k N}

/-- Compatibility with the original theory API. The lift itself is proved
from the actual lattice definition and uses no field of Theory. -/
theorem Theory.interval_lift (_T : Theory k N) (Λ : Lattice k N)
    (A : Submodule k (Ambient k N)) (hlower : Λ.space ≤ A)
    (hupper : A ≤ LatticeGallery.expand (shift k N) Λ.space) :
    ∃ M : Lattice k N, M.space = A :=
  LaurentLattice.interval_lift Λ A hlower hupper

/-- The general one-period correspondence is an actual order isomorphism.
Its lattice lift is constructed from the actual subspace; the retained
theory parameter preserves the existing client API. -/
def Theory.intervalIso (T : Theory k N) (Λ : Lattice k N) :
    {M : Lattice k N // Λ.space ≤ M.space ∧
      M.space ≤ LatticeGallery.expand (shift k N) Λ.space} ≃o
      Set.Icc Λ.space (LatticeGallery.expand (shift k N) Λ.space) where
  toFun M := ⟨M.val.space,M.property⟩
  invFun A := ⟨Classical.choose (T.interval_lift Λ A.val A.property.1 A.property.2),
    by rw [Classical.choose_spec (T.interval_lift Λ A.val A.property.1 A.property.2)]
       exact A.property⟩
  left_inv M := by
    apply Subtype.ext
    apply Lattice.space_injective
    exact Classical.choose_spec (T.interval_lift Λ M.val.space M.property.1 M.property.2)
  right_inv A := by
    apply Subtype.ext
    exact Classical.choose_spec (T.interval_lift Λ A.val A.property.1 A.property.2)
  map_rel_iff' := Iff.rfl

end Guralnick.LaurentLattice
