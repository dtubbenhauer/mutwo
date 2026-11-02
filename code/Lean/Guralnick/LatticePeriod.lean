import Guralnick.LatticeIntervalLift
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module

/-!
# The dimension of one actual lattice period

Finite torsion-free power-series lattices admit bases. Their Laurent-series
extensions are bases of the actual ambient space. The one-period quotient
is computed by taking constant coefficients in such a basis.
-/
noncomputable section
namespace Guralnick.LaurentLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- A full lattice has a finite power-series basis, by the PID theorem. -/
def latticeBasisData (Λ : Lattice k N) :
    Σ r : ℕ, Basis (Fin r) (PowerSeries k) Λ.module := by
  letI : Module.Finite (PowerSeries k) Λ.module := Module.Finite.iff_fg.mpr Λ.finite
  letI : NoZeroSMulDivisors (PowerSeries k) (Ambient k N) := {
    eq_zero_or_eq_zero_of_smul_eq_zero := by
      intro a x h
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        funext i
        have hi := congrFun h i
        change algebraMap (PowerSeries k) (LaurentSeries k) a * x i = 0 at hi
        apply (mul_eq_zero.mp hi).resolve_left
        intro ha0
        exact ha (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
          (by simpa using ha0)) }
  exact Module.basisOfFiniteTypeTorsionFree'

/-- Extending the basis of a lattice to Laurent scalars spans the ambient space. -/
theorem latticeBasis_span {r : ℕ} (Λ : Lattice k N)
    (b : Basis (Fin r) (PowerSeries k) Λ.module) :
    Submodule.span (LaurentSeries k) (Set.range fun i => (b i).val) = ⊤ := by
  have hs : Submodule.span (PowerSeries k) (Set.range fun i => (b i).val) = Λ.module := by
    rw [show (Set.range fun i => (b i).val) = Λ.module.subtype '' Set.range b from
      Set.range_comp _ _, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  rw [← Submodule.span_span_of_tower (PowerSeries k), hs]
  exact Λ.spanning

/-- The same basis is independent over the Laurent-series fraction field. -/
theorem latticeBasis_independent {r : ℕ} (Λ : Lattice k N)
    (b : Basis (Fin r) (PowerSeries k) Λ.module) :
    LinearIndependent (LaurentSeries k) (fun i => (b i).val) := by
  apply (LinearIndependent.iff_fractionRing (PowerSeries k) (LaurentSeries k)).mp
  exact b.linearIndependent.map' Λ.module.subtype (Submodule.ker_subtype _)

/-- The lattice basis has exactly the ambient rank. -/
theorem latticeBasis_card {r : ℕ} (Λ : Lattice k N)
    (b : Basis (Fin r) (PowerSeries k) Λ.module) : r = N := by
  let B := Basis.mk (latticeBasis_independent Λ b) (le_of_eq (latticeBasis_span Λ b).symm)
  have h := Module.finrank_eq_card_basis B
  simpa using h.symm

/-- A power-series basis indexed by the actual ambient coordinates. -/
def latticeBasis (Λ : Lattice k N) : Basis (Fin N) (PowerSeries k) Λ.module :=
  (latticeBasisData Λ).2.reindex (finCongr (latticeBasis_card Λ (latticeBasisData Λ).2))


/-- Return an expanded lattice vector to the lattice by multiplication by t. -/
def periodBack (Λ : Lattice k N) :
    LatticeGallery.expand (shift k N) Λ.space →ₗ[k] Λ.module where
  toFun x := ⟨(PowerSeries.X : PowerSeries k) • x.val,
    X_smul_mem_of_le_expand Λ _ le_rfl x.property⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' a x := by
    apply Subtype.ext
    exact smul_comm (PowerSeries.X : PowerSeries k) a x.val

/-- The actual shifted vector, with its lattice-membership witness. -/
def periodVector (Λ : Lattice k N) (x : Λ.module) :
    LatticeGallery.expand (shift k N) Λ.space :=
  ⟨shift k N x.val, ⟨x.val, x.property, rfl⟩⟩

@[simp] theorem periodBack_vector (Λ : Lattice k N) (x : Λ.module) :
    periodBack Λ (periodVector Λ x) = x := by
  apply Subtype.ext
  exact X_smul_shift x.val

/-- Constant coefficients, coordinate by coordinate. -/
def periodConstants : (Fin N → PowerSeries k) →ₗ[k] (Fin N → k) where
  toFun f i := PowerSeries.constantCoeff k (f i)
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp [PowerSeries.constantCoeff_smul]

/-- Read the actual coordinates of t*x modulo t in a power-series basis. -/
def periodCoefficients (Λ : Lattice k N) :
    LatticeGallery.expand (shift k N) Λ.space →ₗ[k] (Fin N → k) :=
  periodConstants.comp (((latticeBasis Λ).equivFun.restrictScalars k).toLinearMap.comp
    (periodBack Λ))

@[simp] theorem periodCoefficients_apply (Λ : Lattice k N)
    (x : LatticeGallery.expand (shift k N) Λ.space) (i : Fin N) :
    periodCoefficients Λ x i =
      PowerSeries.constantCoeff k ((latticeBasis Λ).equivFun (periodBack Λ x) i) := rfl

/-- Every residue coordinate vector occurs in the period quotient. -/
theorem periodCoefficients_surjective (Λ : Lattice k N) :
    Function.Surjective (periodCoefficients Λ) := by
  intro a
  refine ⟨periodVector Λ ((latticeBasis Λ).equivFun.symm
    (fun i => PowerSeries.C k (a i))), ?_⟩
  ext i
  simp only [periodCoefficients_apply, periodBack_vector, LinearEquiv.apply_symm_apply,
    PowerSeries.constantCoeff_C]

/-- The kernel consists exactly of the unshifted lattice, not merely a
subspace with the expected dimension. -/
theorem periodCoefficients_kernel (Λ : Lattice k N) :
    LinearMap.ker (periodCoefficients Λ) =
      Λ.space.comap (LatticeGallery.expand (shift k N) Λ.space).subtype := by
  classical
  ext x
  change periodCoefficients Λ x = 0 ↔ x.val ∈ Λ.module
  constructor
  · intro hx
    have hd : ∀ i : Fin N, ∃ g : PowerSeries k,
        (latticeBasis Λ).equivFun (periodBack Λ x) i = PowerSeries.X * g := by
      intro i
      apply PowerSeries.X_dvd_iff.mpr
      exact congrFun hx i
    choose g hg using hd
    let z : Λ.module := (latticeBasis Λ).equivFun.symm g
    have hz : (PowerSeries.X : PowerSeries k) • z = periodBack Λ x := by
      apply (latticeBasis Λ).equivFun.injective
      funext i
      simp only [map_smul, LinearEquiv.apply_symm_apply, z, Pi.smul_apply, smul_eq_mul]
      exact (hg i).symm
    have hv : z.val = x.val :=
      X_smul_injective (congrArg Subtype.val hz)
    rw [← hv]
    exact z.property
  · intro hx
    let z : Λ.module := ⟨x.val,hx⟩
    have hz : periodBack Λ x = (PowerSeries.X : PowerSeries k) • z := rfl
    ext i
    simp only [periodCoefficients_apply, hz, map_smul, Pi.smul_apply, smul_eq_mul,
      map_mul, PowerSeries.constantCoeff_X, zero_mul, Pi.zero_apply]

/-- A literal linear equivalence between the actual one-period quotient
and the coordinate vector space k^N. -/
def periodEquiv (Λ : Lattice k N) :
    LatticeGallery.QuotientSpace Λ.space
      (LatticeGallery.expand (shift k N) Λ.space) ≃ₗ[k] (Fin N → k) :=
  (Submodule.quotEquivOfEq _ _ (periodCoefficients_kernel Λ).symm).trans
    ((periodCoefficients Λ).quotKerEquivOfSurjective (periodCoefficients_surjective Λ))

/-- The equivalence reads exactly the specified residue coordinates on representatives. -/
@[simp] theorem periodEquiv_mk (Λ : Lattice k N)
    (x : LatticeGallery.expand (shift k N) Λ.space) :
    periodEquiv Λ (Submodule.Quotient.mk x) = periodCoefficients Λ x := rfl

/-- The actual one-period quotient is finite dimensional over k. -/
theorem period_finite (Λ : Lattice k N) :
    FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space
      (LatticeGallery.expand (shift k N) Λ.space)) :=
  FiniteDimensional.of_injective (periodEquiv Λ).toLinearMap (periodEquiv Λ).injective

/-- The dimension of an actual lattice period equals the ambient rank. -/
theorem period_dimension (Λ : Lattice k N) :
    Module.finrank k (LatticeGallery.QuotientSpace Λ.space
      (LatticeGallery.expand (shift k N) Λ.space)) = N := by
  simpa using (periodEquiv Λ).finrank_eq

#print axioms latticeBasis_card
#print axioms period_finite
#print axioms period_dimension
end Guralnick.LaurentLattice
