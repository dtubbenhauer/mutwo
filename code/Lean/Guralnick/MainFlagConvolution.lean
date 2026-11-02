import Guralnick.FlagConvolution
import Guralnick.SixFlagGallery
import Guralnick.FiniteBlocks

/-!
# The main six-map word inside the general convolution model

The intermediate flags of the recursive integral chain are exactly the
five intermediate flags in the manuscript's retained-mask description.
This is an explicit equivalence, not an input to the convolution theorem.
-/

noncomputable section
namespace Guralnick.FlagConvolution
open ParabolicWeb CanonicalChains LatticeFlags

variable {k : Type} [Field k] {m : ℕ}

def mainGalleryEquiv (source : Flag k (2*m+1) (retained (ParabolicWeb.Family.source m)))
    (target : Flag k (2*m+1) (retained (ParabolicWeb.Family.output m))) :
    Gallery k (mainChain m) source target ≃ LatticeFlags.Family.SixGallery source target := by
  simp only [mainChain, Gallery]
  rw [main_meet_source m, main_meet_cyclic m, main_meet_middle m]
  refine {
    toFun := fun x => ?_
    invFun := fun g =>
      ⟨g.middle, ⟨g.cyclic, ⟨source, ⟨rfl⟩, ⟨g.first, g.step1, g.step2⟩⟩,
        ⟨g.firstCommon, g.step3, g.step4⟩⟩, ⟨g.secondCommon, g.step5, g.step6⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · rcases x with ⟨middle, ⟨cyclic, ⟨src, heq, first⟩, common⟩, last⟩
    obtain ⟨rfl⟩ := heq
    exact {
      first := first.val
      cyclic := cyclic
      firstCommon := common.val
      middle := middle
      secondCommon := last.val
      step1 := first.property.1
      step2 := first.property.2
      step3 := common.property.1
      step4 := common.property.2
      step5 := last.property.1
      step6 := last.property.2 }
  · rintro ⟨middle, ⟨cyclic, ⟨src, heq, first⟩, common⟩, last⟩
    obtain ⟨rfl⟩ := heq
    rfl
  · intro g
    cases g
    rfl

theorem main_gallery_card (source : Flag k (2*m+1) (retained (ParabolicWeb.Family.source m)))
    (target : Flag k (2*m+1) (retained (ParabolicWeb.Family.output m))) :
    Nat.card (Gallery k (mainChain m) source target) =
      Nat.card (LatticeFlags.Family.SixGallery source target) :=
  Nat.card_congr (mainGalleryEquiv source target)

/-- Nonempty convolution galleries force the two one-period endpoint
bounds used for the paper's three-column support restriction. -/
theorem main_endpoint_bounds (hm : 2 ≤ m)
    {source : Flag k (2*m+1) (retained (ParabolicWeb.Family.source m))}
    {target : Flag k (2*m+1) (retained (ParabolicWeb.Family.output m))}
    (h : Nonempty (Gallery k (mainChain m) source target)) :
    (LatticeFlags.Family.sourceNode source).space ≤
      LatticeGallery.expand (LaurentLattice.shift k (2*m+1))
        (LatticeFlags.Family.targetNode target).space ∧
    (LatticeFlags.Family.targetNode target).space ≤
      LatticeGallery.expand (LaurentLattice.shift k (2*m+1))
        (LatticeFlags.Family.sourceNode source).space := by
  obtain ⟨g⟩ := h
  exact LatticeFlags.Family.endpoint_bounds hm (mainGalleryEquiv source target g)

end Guralnick.FlagConvolution
