import Guralnick.LatticeFlagExtension
import Guralnick.PolynomialFullGallery

/-!
# Full refinement exists for every actual polynomial partial flag

Complete the actual lattices, complete their one-period vector-space flag,
and algebraize each resulting lattice. The previously proved inverse
comparison ensures that every original polynomial node is retained.
-/
noncomputable section
namespace Guralnick.PolynomialFlagExtension
open PolynomialFlags PolynomialFullGallery LatticeFlags
variable {k : Type} [Field k] {n : ℕ} [NeZero n]

theorem exists_full_refinement {S : Finset (Fin n)}
    (F : PolynomialFlags.Flag k n S) (hS : S.Nonempty) :
    ∃ E : PolynomialFlags.Flag k n Finset.univ,
      E.restrict (Finset.subset_univ S)=F := by
  obtain ⟨E,hE⟩ := LatticeFlagExtension.exists_full_refinement (completeFlag F) hS
  refine ⟨algebraizeFlag E,?_⟩
  apply (flagEquiv S).injective
  change completeFlag ((algebraizeFlag E).restrict (Finset.subset_univ S))=completeFlag F
  rw [complete_restrict,complete_algebraizeFlag]
  exact hE

/-- Every actual partial polynomial flag has a full lift. No existence or
fiber-cardinality hypothesis is passed to this theorem. -/
theorem lift_nonempty {I : ParabolicWeb.Index n}
    (F : PolynomialFlags.Flag k n (retained I)) : Nonempty (Lift F) := by
  have hS : (retained I).Nonempty := FlagConvolution.retained_nonempty I
  obtain ⟨E,hE⟩ := exists_full_refinement F hS
  have hex : ∃ E : FullFlag k n, forget I E=F := by
    simpa only [FullFlag,fullIndex,retained,Finset.compl_empty,forget,
      retained_subset_full] using (show ∃ E : PolynomialFlags.Flag k n Finset.univ,
        E.restrict (Finset.subset_univ (retained I))=F from ⟨E,hE⟩)
  obtain ⟨E,hE⟩ := hex
  exact ⟨⟨E,hE⟩⟩

/-- Over a finite field the actual full-refinement fiber has positive
cardinality, derived from its independent finiteness and constructed point. -/
theorem lift_card_pos [Finite k] {I : ParabolicWeb.Index n}
    (F : PolynomialFlags.Flag k n (retained I)) : 0<Nat.card (Lift F) := by
  letI := lift_nonempty F
  exact Nat.card_pos

/-- Forgetting no nodes is the identity on an actual full flag. -/
@[simp] theorem forget_full (E : FullFlag k n) : forget (fullIndex n) E=E := by
  apply PolynomialFlags.Flag.ext
  funext i
  rfl

/-- The full-mask boundary case has exactly one full refinement. -/
def fullLiftEquiv (E : FullFlag k n) : Lift E ≃ Unit where
  toFun _ := Unit.unit
  invFun _ := ⟨E,forget_full E⟩
  left_inv A := by
    apply Subtype.ext
    exact (forget_full A.val).symm.trans A.property |>.symm
  right_inv _ := rfl

theorem full_lift_card (E : FullFlag k n) : Nat.card (Lift E)=1 := by
  rw [Nat.card_congr (fullLiftEquiv E)]
  simp

#print axioms lift_nonempty
#print axioms lift_card_pos
#print axioms full_lift_card
end Guralnick.PolynomialFlagExtension
