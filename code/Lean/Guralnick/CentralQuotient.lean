import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# First cohomology under a finite quotient with trivial kernel action

This file uses mathlib's actual inflation--restriction sequence. First it
constructs an inflation linear equivalence under an explicit vanishing
hypothesis on the kernel's first cohomology. Then it proves that vanishing
when the kernel is finite, acts trivially, and its order is nonzero in the
coefficient field.

The distinction between `quotientToInvariants` (coefficients in A^S) and
`ofQuotient` (the representation on all of A descended to G/S) is kept
explicit. Their identification requires trivial action of S and is proved
as a representation isomorphism below. No algebraic-group/KL comparison
or highest-weight irreducibility theorem is asserted here.
-/

noncomputable section

universe u

namespace Guralnick.CentralQuotient

open CategoryTheory

variable {k G : Type u} [Field k] [Group G]

abbrev H1 (A : Rep k G) : ModuleCat k := groupCohomology A 1

/-- Exactness makes inflation surjective when the restricted H¹ vanishes. -/
theorem inflation_surjective (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 ((Action.res _ S.subtype).obj A))] :
    Function.Surjective (groupCohomology.H1InfRes A S).f := by
  have hex := groupCohomology.H1InfRes_exact A S
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff] at hex
  intro x
  exact hex x (@Subsingleton.elim
    (H1 ((Action.res _ S.subtype).obj A)) inferInstance _ _)

/-- The actual inflation map, upgraded to a linear equivalence. At this
stage the quotient coefficient module is explicitly the S-invariants. -/
def inflationLinearEquiv (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 ((Action.res _ S.subtype).obj A))] :
    H1 (A.quotientToInvariants S) ≃ₗ[k] H1 A :=
  LinearEquiv.ofBijective (groupCohomology.H1InfRes A S).f.hom
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      inflation_surjective A S⟩

theorem inflation_finrank (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 ((Action.res _ S.subtype).obj A))] :
    Module.finrank k (H1 (A.quotientToInvariants S)) = Module.finrank k (H1 A) :=
  (inflationLinearEquiv A S).finrank_eq

/-- An additive homomorphism from a finite group to a vector space vanishes
when the group's order is nonzero in the field. -/
theorem finite_addHom_eq_zero [Fintype G] (A : Rep k G)
    (hcard : (Fintype.card G : k) ≠ 0) (f : Additive G →+ A) : f = 0 := by
  apply AddMonoidHom.ext
  intro x
  have hx : Fintype.card G • x = 0 := by
    simpa only [Fintype.card_additive] using card_nsmul_eq_zero (x := x)
  have hf : Fintype.card G • f x = 0 := by
    rw [← map_nsmul, hx, map_zero]
  have hf' : (Fintype.card G : k) • f x = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hf
  exact (smul_eq_zero.mp hf').resolve_left hcard

/-- H¹ of a finite trivially acting group vanishes in nonmodular
characteristic. The proof uses mathlib's H¹ ≅ Hom description. -/
def trivial_finite_H1_subsingleton [Fintype G] (A : Rep k G) [A.IsTrivial]
    (hcard : (Fintype.card G : k) ≠ 0) : Subsingleton (H1 A) := by
  let e := (groupCohomology.H1IsoOfIsTrivial A).toLinearEquiv
  refine ⟨fun x y => e.injective ?_⟩
  exact (finite_addHom_eq_zero A hcard (e x)).trans
    (finite_addHom_eq_zero A hcard (e y)).symm

section DescendedCoefficients

variable (A : Rep k G) (S : Subgroup G) [S.Normal]
  [Representation.IsTrivial (A.ρ.comp S.subtype)]

/-- The invariants are the whole underlying module when S acts trivially.
This map records the identification rather than silently replacing A^S by A. -/
def invariantsToModule :
    Representation.invariants (A.ρ.comp S.subtype) ≃ₗ[k] A where
  toFun := Subtype.val
  invFun x := ⟨x, fun s => Representation.isTrivial_apply (A.ρ.comp S.subtype) s x⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equivariance of the inclusion survives descent to the quotient. -/
def quotientInvariantsInclusion : A.quotientToInvariants S ⟶ A.ofQuotient S where
  hom := ModuleCat.ofHom (Representation.invariants (A.ρ.comp S.subtype)).subtype
  comm q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction q using QuotientGroup.induction_on with
    | H g => rfl

/-- The inverse inclusion sends a vector to itself with its proof of
S-invariance. Both directions are morphisms of quotient representations. -/
def quotientInvariantsInverse : A.ofQuotient S ⟶ A.quotientToInvariants S where
  hom := ModuleCat.ofHom (invariantsToModule A S).symm.toLinearMap
  comm q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      rfl

def quotientInvariantsIsoDescended : A.quotientToInvariants S ≅ A.ofQuotient S where
  hom := quotientInvariantsInclusion A S
  inv := quotientInvariantsInverse A S
  hom_inv_id := by
    ext x
    rfl
  inv_hom_id := by
    ext x
    rfl

/-- Inflation for the representation descended on all of A, with the
invariant-module identification included as a proved isomorphism. -/
def descendedInflationLinearEquiv
    [Subsingleton (H1 ((Action.res _ S.subtype).obj A))] :
    H1 (A.ofQuotient S) ≃ₗ[k] H1 A :=
  (((groupCohomology.functor k (G ⧸ S) 1).mapIso
    (quotientInvariantsIsoDescended A S).symm).toLinearEquiv).trans
    (inflationLinearEquiv A S)

omit [S.Normal] in
/-- The vanishing hypothesis used by inflation--restriction is proved,
not postulated, for the finite trivially acting kernel considered here. -/
theorem finite_kernel_H1_vanishes [Fintype S]
    (hcard : (Fintype.card S : k) ≠ 0) :
    Subsingleton (H1 ((Action.res _ S.subtype).obj A)) := by
  letI : Rep.IsTrivial ((Action.res _ S.subtype).obj A) := inferInstanceAs
    (Representation.IsTrivial (A.ρ.comp S.subtype))
  exact trivial_finite_H1_subsingleton ((Action.res _ S.subtype).obj A) hcard

def finiteKernelInflationLinearEquiv [Fintype S]
    (hcard : (Fintype.card S : k) ≠ 0) : H1 (A.ofQuotient S) ≃ₗ[k] H1 A := by
  letI := finite_kernel_H1_vanishes A S hcard
  exact descendedInflationLinearEquiv A S

theorem finite_kernel_finrank [Fintype S] (hcard : (Fintype.card S : k) ≠ 0) :
    Module.finrank k (H1 (A.ofQuotient S)) = Module.finrank k (H1 A) :=
  (finiteKernelInflationLinearEquiv A S hcard).finrank_eq

end DescendedCoefficients

/-- The central-quotient specialization used in the manuscript. The theorem
does not assume that every representation has trivial central character:
the triviality of the center action remains an explicit typeclass hypothesis. -/
theorem central_quotient_finrank (A : Rep k G) [Fintype (Subgroup.center G)]
    [Representation.IsTrivial (A.ρ.comp (Subgroup.center G).subtype)]
    (hcard : (Fintype.card (Subgroup.center G) : k) ≠ 0) :
    Module.finrank k (H1 (A.ofQuotient (Subgroup.center G))) =
      Module.finrank k (H1 A) :=
  finite_kernel_finrank A (Subgroup.center G) hcard

/-- A nontrivial representation of a simple group is faithful. This is a
separate group-theoretic implication; simplicity of a particular PSL group
and nontriviality of a highest-weight module remain application inputs. -/
theorem representation_faithful_of_simple [IsSimpleGroup G] (A : Rep k G)
    (hA : A.ρ ≠ 1) : Function.Injective A.ρ := by
  rcases (inferInstance : A.ρ.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact A.ρ.ker_eq_bot_iff.mp hbot
  · exact (hA (MonoidHom.ker_eq_top_iff.mp htop)).elim

end Guralnick.CentralQuotient
