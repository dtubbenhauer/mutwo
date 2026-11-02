import Guralnick.RationalCoordinateCochains
import Guralnick.SLCoordinateCoalgebra

/-!
# First cohomology in the coordinate-algebra model

The degree-one space below is `A ⊗ k[SL]`, the differential has target
`A ⊗ k[SL] ⊗ k[SL]`, and the boundaries are the image of the tensor
degree-zero differential.  The comparison with `RationalH1` is a proved
linear equivalence of the kernel/image quotients.  The separate literature
theorem is Jantzen I.4.16, identifying this regular bar complex with derived
rational cohomology; no such derived-functor theorem is claimed here.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
noncomputable section
open scoped TensorProduct

namespace Guralnick.RationalCoordinate
open RationalCohomology SLCoordinate

variable {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι]
variable {A : Rep k (SL ι k)} [FiniteDimensional k A]

theorem scalarEvaluateTwo_comultiplication (f : CoordinateAlgebra k ι) (g h : SL ι k) :
    scalarEvaluateTwo ((comultiplication k ι).toLinearMap f) (g,h) = f (g*h) := by
  have he : scalarEvaluateTwo (k := k) (ι := ι) = (pairEvaluation k ι).toLinearMap := by
    apply TensorProduct.ext
    ext f q
    rfl
  rw [he]
  exact comultiplication_eval k ι f g h

/-- The usual tensor regular differential using the constructed matrix coproduct. -/
def dOne (hA : IsPolynomialRepresentation A) :
    CochainsOne k ι A →ₗ[k] CochainsTwo k ι A :=
  differentialOne (comultiplication k ι).toLinearMap hA

theorem dOne_eval (hA : IsPolynomialRepresentation A) (t : CochainsOne k ι A)
    (g h : SL ι k) :
    evaluateTwo (dOne hA t) (g,h) =
      A.ρ g (evaluateOne t h) - evaluateOne t (g*h) + evaluateOne t g :=
  evaluateTwo_differentialOne _ scalarEvaluateTwo_comultiplication hA t g h

theorem dOne_dZero (hA : IsPolynomialRepresentation A) (a : A) :
    dOne hA (differentialZero hA a) = 0 :=
  differentialOne_differentialZero _ scalarEvaluateTwo_comultiplication hA a

def coordinateCocycles (hA : IsPolynomialRepresentation A) : Submodule k (CochainsOne k ι A) :=
  LinearMap.ker (dOne hA)

theorem mem_coordinateCocycles_iff (hA : IsPolynomialRepresentation A)
    (t : CochainsOne k ι A) :
    t ∈ coordinateCocycles hA ↔ ∀ g h,
      evaluateOne t (g*h) = A.ρ g (evaluateOne t h) + evaluateOne t g := by
  change dOne hA t = 0 ↔ _
  rw [← (evaluateTwo_injective (k := k) (ι := ι) (V := A)).eq_iff]
  simp only [map_zero, funext_iff]
  constructor
  · intro he g h
    have hh := he (g,h)
    rw [dOne_eval] at hh
    change _ = (0 : A) at hh
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh
  · intro he gh
    rcases gh with ⟨g,h⟩
    rw [dOne_eval, he g h]
    simp

/-- The equivalence sends a tensor cocycle to its actual regular function. -/
def cocycleEquiv (hA : IsPolynomialRepresentation A) :
    coordinateCocycles hA ≃ₗ[k] rationalCocycles A where
  toFun t := ⟨evaluateOne t.val,
    (mem_rationalCocycles_iff A _).mpr
      ⟨(cochainEquiv t.val).property, (mem_coordinateCocycles_iff hA t.val).mp t.property⟩⟩
  invFun f := ⟨cochainEquiv.symm ⟨f.val, f.property.1⟩, by
    rw [mem_coordinateCocycles_iff]
    simp only [evaluateOne_cochainEquiv_symm]
    exact (mem_rationalCocycles_iff A f.val).mp f.property |>.2⟩
  left_inv t := by
    apply Subtype.ext
    apply evaluateOne_injective
    exact evaluateOne_cochainEquiv_symm _
  right_inv f := Subtype.ext (evaluateOne_cochainEquiv_symm _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem cocycleEquiv_val (hA : IsPolynomialRepresentation A)
    (t : coordinateCocycles hA) :
    (cocycleEquiv hA t).val = evaluateOne t.val := rfl

def coordinateCoboundary (hA : IsPolynomialRepresentation A) :
    A →ₗ[k] coordinateCocycles hA :=
  (differentialZero hA).codRestrict (coordinateCocycles hA)
    (fun a => dOne_dZero hA a)

def coordinateBoundaries (hA : IsPolynomialRepresentation A) :
    Submodule k (coordinateCocycles hA) := LinearMap.range (coordinateCoboundary hA)

/-- First cohomology of the actual degree-zero/one regular tensor complex. -/
abbrev CoordinateH1 (hA : IsPolynomialRepresentation A) :=
  coordinateCocycles hA ⧸ coordinateBoundaries hA

theorem cocycleEquiv_coboundary (hA : IsPolynomialRepresentation A) (a : A) :
    cocycleEquiv hA (coordinateCoboundary hA a) = regularCoboundary hA a := by
  apply Subtype.ext
  ext g
  exact evaluateOne_differentialZero hA a g

theorem cocycleEquiv_boundaries (hA : IsPolynomialRepresentation A) :
    (coordinateBoundaries hA).map (cocycleEquiv hA).toLinearMap = rationalBoundaries A := by
  rw [rationalBoundaries_eq_range hA]
  ext f
  constructor
  · rintro ⟨t, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (cocycleEquiv_coboundary hA a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨coordinateCoboundary hA a, ⟨a, rfl⟩, cocycleEquiv_coboundary hA a⟩

/-- No cohomological interpretation is assumed in this comparison: both
quotients and the connecting map have been constructed and checked. -/
def h1Equiv (hA : IsPolynomialRepresentation A) : CoordinateH1 hA ≃ₗ[k] RationalH1 A :=
  Submodule.Quotient.equiv _ _ (cocycleEquiv hA) (cocycleEquiv_boundaries hA)

theorem h1_finrank (hA : IsPolynomialRepresentation A) :
    Module.finrank k (CoordinateH1 hA) = Module.finrank k (RationalH1 A) :=
  (h1Equiv hA).finrank_eq

@[simp] theorem h1Equiv_mk (hA : IsPolynomialRepresentation A)
    (t : coordinateCocycles hA) :
    h1Equiv hA (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (cocycleEquiv hA t) := rfl

/-- A convention check: a tensor cocycle has value zero at the group identity. -/
theorem cocycle_identity (hA : IsPolynomialRepresentation A) (t : coordinateCocycles hA) :
    evaluateOne t.val 1 = 0 :=
  groupCohomology.oneCocycles_map_one (forgetRegularity A (cocycleEquiv hA t))

/-- The empty matrix boundary case: the determinant-one group is trivial,
so every regular tensor cocycle is zero. -/
theorem empty_rank_cocycles_subsingleton {A : Rep k (SL (Fin 0) k)}
    [FiniteDimensional k A] (hA : IsPolynomialRepresentation A) :
    Subsingleton (coordinateCocycles hA) := by
  constructor
  intro t u
  apply Subtype.ext
  apply evaluateOne_injective
  ext g
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg, cocycle_identity hA t, cocycle_identity hA u]

end Guralnick.RationalCoordinate
