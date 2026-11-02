import Guralnick.LatticeApproximation

/-!
# Relative quotient and signed-degree preservation

The quotient comparison is induced by the actual ambient inclusion.
Its inverse exists because every completed vector can be represented by
an element of its polynomial lattice modulo the lower lattice.
-/
noncomputable section
namespace Guralnick.LatticeCompletion
variable {k : Type*} [Field k] {N : ℕ}

/-- Natural k-linear inclusion on one actual lattice. -/
def latticeInclusion (M : PolynomialLattice.Lattice k N) :
    M.space →ₗ[k] (complete M).space :=
  (PolynomialLattice.vectorInclusionLinear k N).restrict
    (fun _ hx => mem_completeModule hx)

/-- The actual map on relative quotients induced by coefficient inclusion. -/
def quotientMap (Λ M : PolynomialLattice.Lattice k N) :
    LatticeGallery.QuotientSpace Λ.space M.space →ₗ[k]
      LatticeGallery.QuotientSpace (complete Λ).space (complete M).space :=
  (Λ.space.comap M.space.subtype).mapQ
    ((complete Λ).space.comap (complete M).space.subtype) (latticeInclusion M)
    (by intro x hx; exact mem_completeModule hx)

@[simp] theorem quotientMap_mk (Λ M : PolynomialLattice.Lattice k N) (x : M.space) :
    quotientMap Λ M (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (latticeInclusion M x) := rfl

/-- No nonzero polynomial quotient class vanishes after completion. -/
theorem quotientMap_injective (Λ M : PolynomialLattice.Lattice k N) :
    Function.Injective (quotientMap Λ M) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro q hq
  obtain ⟨x,rfl⟩ := (Λ.space.comap M.space.subtype).mkQ_surjective q
  change quotientMap Λ M (Submodule.Quotient.mk x) = 0 at hq
  rw [quotientMap_mk,Submodule.Quotient.mk_eq_zero] at hq
  change PolynomialLattice.vectorInclusion k N x.val ∈ (complete Λ).module at hq
  have hx := (complete_mem_iff Λ x.val).mp hq
  exact (Submodule.Quotient.mk_eq_zero _).mpr hx

/-- Every completed relative quotient class has a polynomial representative. -/
theorem quotientMap_surjective (Λ M : PolynomialLattice.Lattice k N) :
    Function.Surjective (quotientMap Λ M) := by
  intro q
  obtain ⟨x,rfl⟩ := ((complete Λ).space.comap (complete M).space.subtype).mkQ_surjective q
  obtain ⟨r,hr⟩ := polynomial_lower_bound Λ
  obtain ⟨s,hs⟩ := PolynomialLattice.exists_X_pow_smul_le k N
    (PolynomialLattice.standardLattice k N) M
  obtain ⟨y,hy,he⟩ := approximate_in_complete M.module s hs r x.property
  refine ⟨Submodule.Quotient.mk (⟨y,hy⟩ : M.space),?_⟩
  rw [quotientMap_mk]
  apply (Submodule.Quotient.eq _).mpr
  change PolynomialLattice.vectorInclusion k N y - x.val ∈ (complete Λ).module
  have hh : x.val - PolynomialLattice.vectorInclusion k N y ∈ (complete Λ).module :=
    small_le_complete r hr he
  simpa only [neg_sub] using (complete Λ).module.neg_mem hh

/-- Actual relative-quotient equivalence, including nonnested pairs. -/
def quotientEquiv (Λ M : PolynomialLattice.Lattice k N) :
    LatticeGallery.QuotientSpace Λ.space M.space ≃ₗ[k]
      LatticeGallery.QuotientSpace (complete Λ).space (complete M).space :=
  LinearEquiv.ofBijective (quotientMap Λ M)
    ⟨quotientMap_injective Λ M,quotientMap_surjective Λ M⟩

/-- Polynomial relative quotients are finite-dimensional. Their finiteness
is transported by the actual quotient equivalence, not inferred from a
numerical equality of finranks. -/
theorem quotient_finite (Λ M : PolynomialLattice.Lattice k N) :
    FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space M.space) := by
  let I := LaurentLattice.interLattice (complete Λ) (complete M)
  letI : FiniteDimensional k
      (LatticeGallery.QuotientSpace I.space (complete M).space) :=
    LaurentLattice.finite_quotient I (complete M)
      (LaurentLattice.interLattice_le_right _ _)
  have heq : I.space.comap (complete M).space.subtype =
      (complete Λ).space.comap (complete M).space.subtype := by
    ext x
    change (x.val ∈ (complete Λ).space ∧ x.val ∈ (complete M).space) ↔
      x.val ∈ (complete Λ).space
    exact and_iff_left x.property
  let e : LatticeGallery.QuotientSpace I.space (complete M).space ≃ₗ[k]
      LatticeGallery.QuotientSpace (complete Λ).space (complete M).space :=
    Submodule.quotEquivOfEq _ _ heq
  letI : FiniteDimensional k
      (LatticeGallery.QuotientSpace (complete Λ).space (complete M).space) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  exact FiniteDimensional.of_injective (quotientEquiv Λ M).toLinearMap
    (quotientEquiv Λ M).injective

theorem quotient_finrank (Λ M : PolynomialLattice.Lattice k N) :
    Module.finrank k (LatticeGallery.QuotientSpace Λ.space M.space) =
      Module.finrank k (LatticeGallery.QuotientSpace (complete Λ).space (complete M).space) :=
  (quotientEquiv Λ M).finrank_eq

end Guralnick.LatticeCompletion

namespace Guralnick.PolynomialLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- Signed degree in the independent polynomial model, defined from its own
actual relative quotients and its own standard lattice. -/
def degree (Λ : Lattice k N) : ℤ :=
  let S := (standardModule k N).restrictScalars k
  (Module.finrank k (LatticeGallery.QuotientSpace (Λ.space ⊓ S) Λ.space) : ℤ) -
    Module.finrank k (LatticeGallery.QuotientSpace (Λ.space ⊓ S) S)

end Guralnick.PolynomialLattice

namespace Guralnick.LatticeCompletion
variable {k : Type*} [Field k] {N : ℕ}

/-- Intersection in the denominator simply records the relative quotient. -/
theorem quotient_inf_left {V : Type*} [AddCommGroup V] [Module k V]
    (A B : Submodule k V) : (A ⊓ B).comap A.subtype = B.comap A.subtype := by
  ext x
  simp only [Submodule.mem_comap,Submodule.mem_inf]
  exact and_iff_right x.property

theorem quotient_inf_right {V : Type*} [AddCommGroup V] [Module k V]
    (A B : Submodule k V) : (A ⊓ B).comap B.subtype = A.comap B.subtype := by
  ext x
  simp only [Submodule.mem_comap,Submodule.mem_inf]
  exact and_iff_left x.property

theorem quotient_inf_left_finrank {V : Type*} [AddCommGroup V] [Module k V]
    (A B : Submodule k V) :
    Module.finrank k (LatticeGallery.QuotientSpace (A ⊓ B) A) =
      Module.finrank k (LatticeGallery.QuotientSpace B A) :=
  (Submodule.quotEquivOfEq _ _ (quotient_inf_left A B)).finrank_eq

theorem quotient_inf_right_finrank {V : Type*} [AddCommGroup V] [Module k V]
    (A B : Submodule k V) :
    Module.finrank k (LatticeGallery.QuotientSpace (A ⊓ B) B) =
      Module.finrank k (LatticeGallery.QuotientSpace A B) :=
  (Submodule.quotEquivOfEq _ _ (quotient_inf_right A B)).finrank_eq

/-- Absolute signed degree is preserved, with no choice of component or offset. -/
theorem complete_degree (Λ : PolynomialLattice.Lattice k N) :
    LaurentLattice.degree k N (complete Λ) = PolynomialLattice.degree Λ := by
  have h₁ := quotient_finrank (PolynomialLattice.standardLattice k N) Λ
  have h₂ := quotient_finrank Λ (PolynomialLattice.standardLattice k N)
  rw [complete_standardLattice] at h₁ h₂
  unfold LaurentLattice.degree PolynomialLattice.degree
  dsimp only
  rw [quotient_inf_left_finrank,quotient_inf_right_finrank,
    quotient_inf_left_finrank,quotient_inf_right_finrank]
  change Module.finrank k (LatticeGallery.QuotientSpace
      ((PolynomialLattice.standardModule k N).restrictScalars k) Λ.space) =
    Module.finrank k (LatticeGallery.QuotientSpace
      ((LaurentLattice.standardModule k N).restrictScalars k) (complete Λ).space) at h₁
  change Module.finrank k (LatticeGallery.QuotientSpace Λ.space
      ((PolynomialLattice.standardModule k N).restrictScalars k)) =
    Module.finrank k (LatticeGallery.QuotientSpace (complete Λ).space
      ((LaurentLattice.standardModule k N).restrictScalars k)) at h₂
  exact congrArg₂ (fun (a b : ℕ) => (a : ℤ) - b) h₁.symm h₂.symm

#print axioms quotientEquiv
#print axioms complete_degree
end Guralnick.LatticeCompletion
