import Guralnick.PolynomialFlags

/-! # Full flag lifts of the actual partial galleries

A full lift remembers every intermediate lattice, not only a dimension
count. The full-gallery type is the chain counted by a product of finite
parabolic indicator kernels in complete-flag convolution.
-/
noncomputable section
namespace Guralnick.PolynomialFullGallery
open ParabolicWeb CanonicalChains LatticeFlags PolynomialFlags
variable {k : Type} [Field k] {n : ℕ} [NeZero n]

def fullIndex (n : ℕ) [NeZero n] : Index n :=
  ⟨∅,by
    intro h
    have hm := Finset.mem_univ (⟨0,NeZero.pos n⟩ : Fin n)
    rw [←h] at hm
    exact Finset.notMem_empty _ hm⟩

abbrev FullFlag (k : Type) [Field k] (n : ℕ) [NeZero n] :=
  PolynomialFlags.Flag k n (retained (fullIndex n))

theorem retained_subset_full (I : Index n) : retained I⊆retained (fullIndex n) := by
  simp [retained,fullIndex]

def forget (I : Index n) (E : FullFlag k n) : PolynomialFlags.Flag k n (retained I) :=
  E.restrict (retained_subset_full I)

def Lift {I : Index n} (F : PolynomialFlags.Flag k n (retained I)) :=
  {E : FullFlag k n // forget I E=F}

/-- A full lift is one of the finitely many possible full middle flags
bounded by the retained target flag. -/
def liftToPossible {I : Index n} (F : PolynomialFlags.Flag k n (retained I))
    (E : Lift F) : FlagConvolution.PossibleMiddle k (fullIndex n) I (completeFlag F) := by
  refine ⟨completeFlag E.val,?_⟩
  let R := (completeFlag E.val).restrict (retained_subset_full (meet (fullIndex n) I))
  refine ⟨R,?_,?_⟩
  · intro i hi hj
    rfl
  · intro i hi hj
    have h := congrArg (fun G : PolynomialFlags.Flag k n (retained I) => G.node ⟨i,hj⟩) E.property
    exact congrArg LatticeCompletion.complete h

theorem liftToPossible_injective {I : Index n} (F : PolynomialFlags.Flag k n (retained I)) :
    Function.Injective (liftToPossible F) := by
  intro E E' h
  apply Subtype.ext
  apply (flagEquiv (retained (fullIndex n))).injective
  exact congrArg Subtype.val h

instance lift_finite [Finite k] {I : Index n} (F : PolynomialFlags.Flag k n (retained I)) :
    Finite (Lift F) := by
  letI := FlagConvolution.possibleMiddle_finite k (fullIndex n) I (completeFlag F)
  exact Finite.of_injective (liftToPossible F) (liftToPossible_injective F)

/-- Complete-flag chain for the product x_(I_r)...x_(I_0). A chain with
no steps still contains its one parabolic agreement condition. -/
def FullGallery : {I J : Index n} → Chain I J → FullFlag k n → FullFlag k n → Type
  | _, _, .nil I, source, target => PLift (forget I source=forget I target)
  | _, _, .snoc path T, source, target =>
      (middle : FullFlag k n) × FullGallery path source middle ×
        PLift (forget T middle=forget T target)

/-- One independent full lift for every actual common-facet refinement. -/
def Decorations : {I J : Index n} → (path : Chain I J) →
    {source : PolynomialFlags.Flag k n (retained I)} →
    {target : PolynomialFlags.Flag k n (retained J)} → PolynomialFlags.Gallery path source target → Type
  | _, _, .nil _, _, _, _ => Unit
  | _, _, .snoc (J := J) path T, source, target, g => by
      simp only [PolynomialFlags.Gallery] at g
      exact Decorations path g.2.1 × Lift g.2.2.val

instance decorations_finite [Finite k] {I J : Index n} (path : Chain I J)
    {source : PolynomialFlags.Flag k n (retained I)}
    {target : PolynomialFlags.Flag k n (retained J)} (g : PolynomialFlags.Gallery path source target) :
    Finite (Decorations path g) := by
  induction path with
  | nil => simp only [Decorations]; infer_instance
  | snoc path T ih =>
    simp only [Decorations]
    haveI : ∀ {target : PolynomialFlags.Flag k n (retained _)}
        (g : PolynomialFlags.Gallery path source target), Finite (Decorations path g) := ih
    infer_instance

#print axioms lift_finite
#print axioms decorations_finite
end Guralnick.PolynomialFullGallery
