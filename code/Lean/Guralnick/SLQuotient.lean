import Guralnick.HighestWeight
import Guralnick.CentralQuotient
import Guralnick.FiniteCohomology
import Mathlib.FieldTheory.Finite.Basic

/-!
# Concrete SL-to-PSL descent

The center order is bounded by the cardinality of the prime field's unit
group, so its invertibility is proved. Root-lattice highest weights have
trivial central action by the actual torus/fixed-vector argument. The
quotient representation preserves irreducibility and nontriviality and
has the same actual first cohomology dimension.
-/

noncomputable section
namespace Guralnick.SLQuotient
open HighestWeight

variable {k G : Type} [Field k] [Group G]

theorem quotient_irreducible (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (A.ρ.comp S.subtype)]
    (hA : Cohomology.Irreducible A) : Cohomology.Irreducible (A.ofQuotient S) := by
  refine ⟨hA.1, ?_⟩
  intro V hV
  exact hA.2 V (fun g x hx => hV (g : G ⧸ S) x hx)

theorem quotient_nontrivial (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (A.ρ.comp S.subtype)]
    (hA : A.ρ ≠ 1) : (A.ofQuotient S).ρ ≠ 1 := by
  intro h
  apply hA
  apply MonoidHom.ext
  intro g
  exact congrArg (fun ρ => ρ (g : G ⧸ S)) h

noncomputable instance centerFintype (n p : ℕ) [Fact p.Prime] :
    Fintype (Subgroup.center (SL n (ZMod p))) := Fintype.ofFinite _

theorem center_card_lt_prime (n p : ℕ) (hn : 0 < n) [Fact p.Prime] :
    Fintype.card (Subgroup.center (SL n (ZMod p))) < p := by
  let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (R := ZMod p) (⟨0, hn⟩ : Fin n)
  have hle : Fintype.card (Subgroup.center (SL n (ZMod p))) ≤
      Fintype.card (ZMod p)ˣ :=
    Fintype.card_le_of_injective (fun z => (e z).val)
      (Subtype.val_injective.comp e.injective)
  rw [ZMod.card_units] at hle
  have hp := (Fact.out : p.Prime).pos
  omega

theorem center_order_invertible (n p : ℕ) (hn : 0 < n) [Fact p.Prime] :
    (Fintype.card (Subgroup.center (SL n (ZMod p))) : Cohomology.PrimeClosure p) ≠ 0 := by
  intro hz
  have hdiv := (CharP.cast_eq_zero_iff (Cohomology.PrimeClosure p) p
    (Fintype.card (Subgroup.center (SL n (ZMod p))))).mp hz
  exact Nat.not_dvd_of_pos_of_lt Fintype.card_pos (center_card_lt_prime n p hn) hdiv

theorem restriction_center_trivial (n p : ℕ) (hn : 0 < n) [Fact p.Prime]
    (wt : Weights.RootLattice n)
    (A : Rep (Cohomology.PrimeClosure p) (SL n (Cohomology.PrimeClosure p)))
    (hA : Cohomology.Irreducible A) (hw : HasHighestWeight A wt.val) :
    Representation.IsTrivial ((restrictPrime n p A).ρ.comp
      (Subgroup.center (SL n (ZMod p))).subtype) := by
  letI := root_lattice_center_trivial hn wt A hA hw
  constructor
  intro z
  apply LinearMap.ext
  intro x
  exact Representation.isTrivial_apply
    (A.ρ.comp (Subgroup.center (SL n (Cohomology.PrimeClosure p))).subtype)
    ⟨Matrix.SpecialLinearGroup.map
        (algebraMap (ZMod p) (Cohomology.PrimeClosure p)) z.val,
      map_center _ z.val z.property⟩ x

/-- The named PSL representation descended from this actual highest-weight
module, using the proved trivial action of the finite center. -/
def descended (n p : ℕ) (hn : 0 < n) [Fact p.Prime]
    (wt : Weights.RootLattice n)
    (A : Rep (Cohomology.PrimeClosure p) (SL n (Cohomology.PrimeClosure p)))
    (hA : Cohomology.Irreducible A) (hw : HasHighestWeight A wt.val) :
    Rep (Cohomology.PrimeClosure p) (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod p)) :=
  letI := restriction_center_trivial n p hn wt A hA hw
  (restrictPrime n p A).ofQuotient (Subgroup.center (SL n (ZMod p)))

theorem descended_h1_dimension (n p : ℕ) (hn : 0 < n) [Fact p.Prime]
    (wt : Weights.RootLattice n)
    (A : Rep (Cohomology.PrimeClosure p) (SL n (Cohomology.PrimeClosure p)))
    (hA : Cohomology.Irreducible A) (hw : HasHighestWeight A wt.val) :
    Cohomology.h1Dimension (descended n p hn wt A hA hw) =
      Cohomology.h1Dimension (restrictPrime n p A) := by
  letI := restriction_center_trivial n p hn wt A hA hw
  exact CentralQuotient.central_quotient_finrank (restrictPrime n p A)
    (center_order_invertible n p hn)

theorem descended_admissible (n p : ℕ) (hn : 0 < n) [Fact p.Prime]
    [IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod p))]
    (wt : Weights.RootLattice n)
    (A : Rep (Cohomology.PrimeClosure p) (SL n (Cohomology.PrimeClosure p)))
    (hA : SimpleHighestWeight A wt.val)
    (hirr : Cohomology.Irreducible (restrictPrime n p A))
    (hne : (restrictPrime n p A).ρ ≠ 1) :
    Cohomology.Admissible (descended n p hn wt A hA.2.1 hA.2.2) := by
  letI := restriction_center_trivial n p hn wt A hA.2.1 hA.2.2
  letI : FiniteDimensional (Cohomology.PrimeClosure p) A := hA.1
  refine ⟨?_, ?_, ?_⟩
  · change FiniteDimensional (Cohomology.PrimeClosure p) A
    exact hA.1
  · exact CentralQuotient.representation_faithful_of_simple _
      (quotient_nontrivial (restrictPrime n p A) _ hne)
  · exact quotient_irreducible (restrictPrime n p A) _ hirr

end Guralnick.SLQuotient
