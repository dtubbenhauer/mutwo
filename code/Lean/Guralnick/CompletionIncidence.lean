import Guralnick.PowerSeriesCompletion
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Finite-dimensional incidence is preserved by completion

The natural finite-quotient comparison acts coordinatewise, carries
submodules to submodules, preserves intersections and sums, and respects
stability under the parameter. The dimensions of subspaces and quotient
spaces are preserved. These are actual maps on ideal quotients.
-/
noncomputable section
namespace Guralnick.PowerSeriesCompletion
variable (k : Type*) [CommRing k] (d N : ℕ)

instance polynomialFinite : Module.Finite k (PolynomialQuotient k d) :=
  (Polynomial.monic_X_pow d).finite_quotient

instance seriesFinite : Module.Finite k (SeriesQuotient k d) :=
  Module.Finite.of_surjective (completion k d).toLinearMap (completion_surjective k d)

abbrev PolynomialVectors := Fin N → PolynomialQuotient k d
abbrev SeriesVectors := Fin N → SeriesQuotient k d

/-- Coordinatewise natural completion on the finite quotient. -/
def vectorEquiv : PolynomialVectors k d N ≃ₗ[k] SeriesVectors k d N :=
  LinearEquiv.piCongrRight fun _ => (completionEquiv k d).toLinearEquiv

def polynomialParameter (x : PolynomialVectors k d N) : PolynomialVectors k d N :=
  fun i => Ideal.Quotient.mk (polynomialIdeal k d) Polynomial.X * x i

def seriesParameter (x : SeriesVectors k d N) : SeriesVectors k d N :=
  fun i => Ideal.Quotient.mk (seriesIdeal k d) PowerSeries.X * x i

/-- The comparison keeps the actual parameter action, not only dimension. -/
theorem vector_parameter (x : PolynomialVectors k d N) :
    vectorEquiv k d N (polynomialParameter k d N x) =
      seriesParameter k d N (vectorEquiv k d N x) := by
  funext i
  exact completion_parameter_mul k d (x i)

/-- Actual subspace incidence is transported by the natural linear map. -/
def subspaceEquiv : Submodule k (PolynomialVectors k d N) ≃o
    Submodule k (SeriesVectors k d N) :=
  Submodule.orderIsoMapComap (vectorEquiv k d N)

theorem subspace_inf (U V : Submodule k (PolynomialVectors k d N)) :
    subspaceEquiv k d N (U ⊓ V) = subspaceEquiv k d N U ⊓ subspaceEquiv k d N V :=
  (subspaceEquiv k d N).map_inf U V

theorem subspace_sup (U V : Submodule k (PolynomialVectors k d N)) :
    subspaceEquiv k d N (U ⊔ V) = subspaceEquiv k d N U ⊔ subspaceEquiv k d N V :=
  (subspaceEquiv k d N).map_sup U V

def PolynomialStable (U : Submodule k (PolynomialVectors k d N)) : Prop :=
  ∀ x ∈ U, polynomialParameter k d N x ∈ U

def SeriesStable (U : Submodule k (SeriesVectors k d N)) : Prop :=
  ∀ x ∈ U, seriesParameter k d N x ∈ U

/-- Exactly the parameter-stable subspaces correspond. -/
theorem stable_iff (U : Submodule k (PolynomialVectors k d N)) :
    SeriesStable k d N (subspaceEquiv k d N U) ↔ PolynomialStable k d N U := by
  constructor
  · intro h x hx
    have hx' : vectorEquiv k d N x ∈ subspaceEquiv k d N U := ⟨x, hx, rfl⟩
    have ht := h _ hx'
    rw [← vector_parameter] at ht
    obtain ⟨y, hy, he⟩ := ht
    have he' := (vectorEquiv k d N).injective he
    simpa only [he'] using hy
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨polynomialParameter k d N y, h y hy, vector_parameter k d N y⟩

/-- Inclusion-preserving bijection on the invariant-subspace configurations
that encode bounded lattice intervals. -/
def stableSubspaceEquiv :
    {U : Submodule k (PolynomialVectors k d N) // PolynomialStable k d N U} ≃o
    {U : Submodule k (SeriesVectors k d N) // SeriesStable k d N U} where
  toFun U := ⟨subspaceEquiv k d N U.val, (stable_iff k d N U.val).mpr U.property⟩
  invFun V := ⟨(subspaceEquiv k d N).symm V.val, by
    apply (stable_iff k d N _).mp
    simpa using V.property⟩
  left_inv U := by apply Subtype.ext; exact (subspaceEquiv k d N).symm_apply_apply U.val
  right_inv V := by apply Subtype.ext; exact (subspaceEquiv k d N).apply_symm_apply V.val
  map_rel_iff' := (subspaceEquiv k d N).map_rel_iff

/-- Natural equivalence of the actual quotient vector spaces. -/
def quotientEquiv (U : Submodule k (PolynomialVectors k d N)) :
    (PolynomialVectors k d N ⧸ U) ≃ₗ[k]
      (SeriesVectors k d N ⧸ subspaceEquiv k d N U) :=
  Submodule.Quotient.equiv U _ (vectorEquiv k d N) rfl

section Field
variable {k : Type*} [Field k]

theorem polynomial_finrank (d : ℕ) : Module.finrank k (PolynomialQuotient k d) = d := by
  simpa [AdjoinRoot.powerBasis'_dim, PolynomialQuotient, polynomialIdeal] using
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (R := k) d)).finrank

theorem series_finrank (d : ℕ) : Module.finrank k (SeriesQuotient k d) = d := by
  rw [← (completionEquiv k d).toLinearEquiv.finrank_eq, polynomial_finrank]

theorem subspace_finrank (d N : ℕ) (U : Submodule k (PolynomialVectors k d N)) :
    Module.finrank k (subspaceEquiv k d N U) = Module.finrank k U :=
  (vectorEquiv k d N).finrank_map_eq U

theorem quotient_finrank (d N : ℕ) (U : Submodule k (PolynomialVectors k d N)) :
    Module.finrank k (PolynomialVectors k d N ⧸ U) =
      Module.finrank k (SeriesVectors k d N ⧸ subspaceEquiv k d N U) :=
  (quotientEquiv k d N U).finrank_eq

end Field
#print axioms stableSubspaceEquiv
#print axioms series_finrank
end Guralnick.PowerSeriesCompletion
