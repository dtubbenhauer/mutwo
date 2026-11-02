import Guralnick.ElementaryCoxeterPackets
import Mathlib.Order.WellFounded
import Mathlib.Data.Fintype.Card

/-!
# Uniqueness of reversal on each actual packet

A finite linearly ordered fiber has at most one decreasing permutation.
Applying this to the concrete interval partition makes the packet-reversal
characterization independent of any Coxeter length formula.
-/

noncomputable section

namespace Guralnick.ElementaryCoxeterPackets

/-- Two permutations preserving the same fibers and decreasing on each
fiber agree. The proof compares their actual restrictions, whose ranges
are the whole fiber. -/
theorem fiber_preserving_strictAnti_unique
    {α β : Type*} [LinearOrder α] [Finite α] (p : α → β)
    (σ τ : Equiv.Perm α)
    (hσ : ∀ i, p (σ i) = p i) (hτ : ∀ i, p (τ i) = p i)
    (haσ : ∀ i j, p i = p j → i < j → σ j < σ i)
    (haτ : ∀ i j, p i = p j → i < j → τ j < τ i) : σ = τ := by
  apply Equiv.ext
  intro i
  let b := p i
  let s : Equiv.Perm {j : α // p j = b} :=
    σ.subtypeEquiv (fun j => by rw [hσ j])
  let t : Equiv.Perm {j : α // p j = b} :=
    τ.subtypeEquiv (fun j => by rw [hτ j])
  have hs : StrictAnti s := by
    intro j k hjk
    exact haσ j.val k.val (j.property.trans k.property.symm) hjk
  have ht : StrictAnti t := by
    intro j k hjk
    exact haτ j.val k.val (j.property.trans k.property.symm) hjk
  have he : (s : _ → _) = t := (hs.range_inj ht).mp (by
    rw [s.surjective.range_eq, t.surjective.range_eq])
  exact congrArg Subtype.val (congrFun he ⟨i, rfl⟩)

/-- A packet-preserving permutation which decreases inside each packet is
unique, for arbitrary packet sizes (including empty packets). -/
theorem packet_permutation_unique (L : List ℕ)
    (σ τ : Equiv.Perm (Fin L.sum))
    (hσ : ∀ i, packet L (σ i) = packet L i)
    (hτ : ∀ i, packet L (τ i) = packet L i)
    (haσ : ∀ i j, packet L i = packet L j → i < j → σ j < σ i)
    (haτ : ∀ i j, packet L i = packet L j → i < j → τ j < τ i) :
    σ = τ :=
  fiber_preserving_strictAnti_unique (packet L) σ τ hσ hτ haσ haτ

#print axioms packet_permutation_unique

end Guralnick.ElementaryCoxeterPackets
