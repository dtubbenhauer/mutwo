import Guralnick.LatticeGallery
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Relative dimensions and equal determinant degree

The dimensions are those of actual vector-space quotients. Equal relative
index of the source vertices is a condition on their quotients in their
common sum. Under that condition the two dimensions assigned to any common
upper lattice agree. This is the dimension comparison needed before the
lattice gallery can be read as a target-quotient flag.
-/

namespace Guralnick.LatticeGallery
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The subquotient `C/(B∩C)` is the actual image of C in A/B. -/
noncomputable def subquotientEquivImage (B C A : Submodule k V) (hCA : C ≤ A) :
    QuotientSpace B C ≃ₗ[k]
      (C.comap A.subtype).map (B.comap A.subtype).mkQ := by
  let f : C →ₗ[k] QuotientSpace B A :=
    (B.comap A.subtype).mkQ.comp (Submodule.inclusion hCA)
  have hker : LinearMap.ker f = B.comap C.subtype := by
    ext x
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.coe_inclusion]
  have hrange : LinearMap.range f =
      (C.comap A.subtype).map (B.comap A.subtype).mkQ := by
    simp only [f, LinearMap.range_comp, Submodule.range_inclusion]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

/-- Additivity of relative dimensions along an actual subspace chain.
Only the largest quotient is required to be finite-dimensional. -/
theorem quotient_chain_dimensions (B C A : Submodule k V)
    (hBC : B ≤ C) (hCA : C ≤ A)
    [FiniteDimensional k (QuotientSpace B A)] :
    Module.finrank k (QuotientSpace C A) +
      Module.finrank k (QuotientSpace B C) =
        Module.finrank k (QuotientSpace B A) := by
  let B' := B.comap A.subtype
  let C' := C.comap A.subtype
  have hle : B' ≤ C' := Submodule.comap_mono hBC
  let e₁ := subquotientEquivImage B C A hCA
  let e₂ := Submodule.quotientQuotientEquivQuotient B' C' hle
  have hdim := (C'.map B'.mkQ).finrank_quotient_add_finrank
  rw [e₂.finrank_eq, ← e₁.finrank_eq] at hdim
  exact hdim

/-- Equal determinant degree expressed by actual finite relative quotients.
Finiteness is imposed at applications, rather than using finrank on an
infinite-dimensional quotient as a degree. -/
def EqualRelativeIndex (Λ Λ' : Submodule k V) : Prop :=
  Module.finrank k (QuotientSpace Λ (Λ ⊔ Λ')) =
    Module.finrank k (QuotientSpace Λ' (Λ ⊔ Λ'))

/-- Equal source-vertex index gives the same dimension above either source.
This is a proof of the dimension transfer, not a new assumed gallery formula. -/
theorem relative_dimensions_equal (Λ Λ' A : Submodule k V)
    (hΛ : Λ ≤ A) (hΛ' : Λ' ≤ A) (hindex : EqualRelativeIndex Λ Λ')
    [FiniteDimensional k (QuotientSpace Λ A)]
    [FiniteDimensional k (QuotientSpace Λ' A)] :
    Module.finrank k (QuotientSpace Λ A) =
      Module.finrank k (QuotientSpace Λ' A) := by
  have hsum : Λ ⊔ Λ' ≤ A := sup_le hΛ hΛ'
  have h₁ := quotient_chain_dimensions Λ (Λ ⊔ Λ') A le_sup_left hsum
  have h₂ := quotient_chain_dimensions Λ' (Λ ⊔ Λ') A le_sup_right hsum
  unfold EqualRelativeIndex at hindex
  omega

/-- The order-correspondence image is the ordinary linear image in U/B. -/
theorem quotientImage_eq_map (B U : Submodule k V) (hBU : B ≤ U)
    (A : Submodule k V) (hBA : B ≤ A) (hAU : A ≤ U) :
    quotientImage B U hBU A hBA hAU =
      (A.comap U.subtype).map (B.comap U.subtype).mkQ := by
  rfl

/-- A quotient image and the relative quotient A/B have the same actual
vector-space dimension, by the first isomorphism theorem. -/
theorem quotientImage_finrank (B U : Submodule k V) (hBU : B ≤ U)
    (A : Submodule k V) (hBA : B ≤ A) (hAU : A ≤ U) :
    Module.finrank k (quotientImage B U hBU A hBA hAU) =
      Module.finrank k (QuotientSpace B A) := by
  rw [quotientImage_eq_map]
  exact (subquotientEquivImage B A U hAU).finrank_eq.symm

/-- The quotient-coordinate dimension of a gallery node agrees with its
source-relative dimension when the two source vertices have equal index. -/
theorem source_dimension_in_target_quotient
    (Λ Λ' U A : Submodule k V) (hΛ'U : Λ' ≤ U)
    (hΛA : Λ ≤ A) (hΛ'A : Λ' ≤ A) (hAU : A ≤ U)
    (hindex : EqualRelativeIndex Λ Λ')
    [FiniteDimensional k (QuotientSpace Λ A)]
    [FiniteDimensional k (QuotientSpace Λ' A)] :
    Module.finrank k (quotientImage Λ' U hΛ'U A hΛ'A hAU) =
      Module.finrank k (QuotientSpace Λ A) := by
  rw [quotientImage_finrank]
  exact (relative_dimensions_equal Λ Λ' A hΛA hΛ'A hindex).symm

end Guralnick.LatticeGallery
