import Guralnick.LatticeTheory

/-! # Comparable full lattices of equal degree coincide -/
namespace Guralnick.LaurentLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- Equal absolute degree and containment leave no nonzero relative
quotient. This handles repeated retained types and zero-dimensional
boundary cases without inserting an extra lattice choice. -/
theorem Theory.eq_of_le_of_degree_eq (T : Theory k N) {Λ M : Lattice k N}
    (hle : Λ ≤ M) (heq : degree k N Λ = degree k N M) : Λ = M := by
  letI := T.finite_quotient Λ M hle
  have hd : Module.finrank k (LatticeGallery.QuotientSpace Λ.space M.space) = 0 := by
    have h := T.dimension_degree Λ M hle
    rw [heq,sub_self] at h
    exact_mod_cast h
  haveI : Subsingleton (LatticeGallery.QuotientSpace Λ.space M.space) :=
    Module.finrank_zero_iff.mp hd
  apply Lattice.space_injective
  apply le_antisymm (show Λ.space ≤ M.space from hle)
  intro x hx
  have hzero : (Submodule.Quotient.mk (⟨x,hx⟩ : M.space) :
      LatticeGallery.QuotientSpace Λ.space M.space) = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero (p := Λ.space.comap M.space.subtype)
    (x := (⟨x,hx⟩ : M.space))).mp hzero

end Guralnick.LaurentLattice
