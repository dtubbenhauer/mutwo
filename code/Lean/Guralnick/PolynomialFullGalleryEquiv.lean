import Guralnick.PolynomialFullGallery

/-! # Actual complete-flag choices over a partial gallery

The last-step equivalence remembers the middle partial flag, its common
refinement and a full lift of that refinement. It is an equivalence of
configuration types, prior to any finite count or Hecke specialization.
-/
noncomputable section
namespace Guralnick.PolynomialFullGallery
open ParabolicWeb CanonicalChains LatticeFlags PolynomialFlags
variable {k : Type} [Field k] {n : ℕ} [NeZero n]


theorem left_retained_le (I J : Index n) : retained I⊆retained (meet I J) := by
  rw [FlagConvolution.retained_meet]
  exact Finset.subset_union_left

theorem right_retained_le (I J : Index n) : retained J⊆retained (meet I J) := by
  rw [FlagConvolution.retained_meet]
  exact Finset.subset_union_right

theorem forget_eq_of_compatible {I R : Index n} (hIR : retained I⊆retained R)
    (F : PolynomialFlags.Flag k n (retained I)) (E : FullFlag k n)
    (h : PolynomialFlags.Compatible F (forget R E)) : forget I E=F := by
  apply PolynomialFlags.Flag.ext
  funext i
  exact (h i.val i.property (hIR i.property)).symm

def refinementFromFull (I J : Index n) (E : FullFlag k n)
    (target : PolynomialFlags.Flag k n (retained J)) (h : forget J E=target) :
    {R : PolynomialFlags.Flag k n (retained (meet I J)) //
      PolynomialFlags.Compatible (forget I E) R ∧ PolynomialFlags.Compatible R target} := by
  refine ⟨forget (meet I J) E,?_,?_⟩
  · intro i hi hj; rfl
  · intro i hi hj
    exact congrArg (fun F : PolynomialFlags.Flag k n (retained J) => F.node ⟨i,hj⟩) h

def LastData (I J : Index n) (P : PolynomialFlags.Flag k n (retained I) → Type)
    (target : PolynomialFlags.Flag k n (retained J)) :=
  (F : PolynomialFlags.Flag k n (retained I)) × P F ×
    ((R : {R : PolynomialFlags.Flag k n (retained (meet I J)) //
      PolynomialFlags.Compatible F R ∧ PolynomialFlags.Compatible R target}) × Lift R.val)

def lastTo (I J : Index n) (P : PolynomialFlags.Flag k n (retained I) → Type)
    (target : PolynomialFlags.Flag k n (retained J))
    (g : (E : FullFlag k n) × P (forget I E) × PLift (forget J E=target)) :
    LastData I J P target :=
  ⟨forget I g.1,g.2.1,refinementFromFull I J g.1 target g.2.2.down,⟨g.1,rfl⟩⟩

def lastFrom (I J : Index n) (P : PolynomialFlags.Flag k n (retained I) → Type)
    (target : PolynomialFlags.Flag k n (retained J)) (g : LastData I J P target) :
    (E : FullFlag k n) × P (forget I E) × PLift (forget J E=target) := by
  let R := g.2.2.1
  let E := g.2.2.2
  have hE : forget (meet I J) E.val = R.val := E.property
  have hFR : PolynomialFlags.Compatible g.1 (forget (meet I J) E.val) := by
    rw [hE]
    exact R.property.1
  have hRT : PolynomialFlags.Compatible (forget (meet I J) E.val) target := by
    rw [hE]
    exact R.property.2
  have hF := forget_eq_of_compatible (left_retained_le I J) g.1 E.val hFR
  have hT := forget_eq_of_compatible (right_retained_le I J) target E.val
    (fun i hi hj => (hRT i hj hi).symm)
  exact ⟨E.val,hF.symm ▸ g.2.1,⟨hT⟩⟩

def lastEquiv (I J : Index n) (P : PolynomialFlags.Flag k n (retained I) → Type)
    (target : PolynomialFlags.Flag k n (retained J)) :
    ((E : FullFlag k n) × P (forget I E) × PLift (forget J E=target)) ≃
      LastData I J P target where
  toFun := lastTo I J P target
  invFun := lastFrom I J P target
  left_inv g := by
    obtain ⟨E,p,⟨h⟩⟩ := g
    subst target
    rfl
  right_inv g := by
    obtain ⟨F,p,⟨R,hFR,hRT⟩,E,hE⟩ := g
    change forget (meet I J) E=R at hE
    subst R
    have hF := forget_eq_of_compatible (left_retained_le I J) F E hFR
    subst F
    rfl

def snocGalleryEquiv {I J : Index n} (path : Chain I J) (T : Index n)
    (source : PolynomialFlags.Flag k n (retained I))
    (target : PolynomialFlags.Flag k n (retained T)) :
    PolynomialFlags.Gallery (.snoc path T) source target ≃
      ((middle : PolynomialFlags.Flag k n (retained J)) ×
        PolynomialFlags.Gallery path source middle ×
          {R : PolynomialFlags.Flag k n (retained (meet J T)) //
            PolynomialFlags.Compatible middle R ∧ PolynomialFlags.Compatible R target}) :=
  Equiv.cast (by rw [PolynomialFlags.Gallery])

def decoratedSnocEquiv {I J : Index n} (path : Chain I J) (T : Index n)
    (source : PolynomialFlags.Flag k n (retained I))
    (target : PolynomialFlags.Flag k n (retained T)) :
    ((g : PolynomialFlags.Gallery (.snoc path T) source target) × Decorations (.snoc path T) g) ≃
      ((g : (middle : PolynomialFlags.Flag k n (retained J)) ×
        PolynomialFlags.Gallery path source middle ×
          {R : PolynomialFlags.Flag k n (retained (meet J T)) //
            PolynomialFlags.Compatible middle R ∧ PolynomialFlags.Compatible R target}) ×
        Decorations path g.2.1 × Lift g.2.2.val) := by
  refine (Equiv.sigmaCongrLeft' (snocGalleryEquiv path T source target)).trans
    (Equiv.sigmaCongrRight fun g => ?_)
  simp only [Decorations]
  let e := snocGalleryEquiv path T source target
  change (Decorations path (e (e.symm g)).2.1 × Lift (e (e.symm g)).2.2.val) ≃
    (Decorations path g.2.1 × Lift g.2.2.val)
  rw [e.apply_symm_apply]

def reassocEquiv {I J : Index n} (path : Chain I J) (T : Index n)
    (source : PolynomialFlags.Flag k n (retained I))
    (target : PolynomialFlags.Flag k n (retained T)) :
    LastData J T (fun F => (g : PolynomialFlags.Gallery path source F) × Decorations path g) target ≃
      ((g : PolynomialFlags.Gallery (.snoc path T) source target) × Decorations (.snoc path T) g) := by
  refine Equiv.trans ?_ (decoratedSnocEquiv path T source target).symm
  exact {
    toFun := fun g => ⟨⟨g.1,g.2.1.1,g.2.2.1⟩,g.2.1.2,g.2.2.2⟩
    invFun := fun g => ⟨g.1.1,⟨g.1.2.1,g.2.1⟩,g.1.2.2,g.2.2⟩
    left_inv := fun g => by cases g; rfl
    right_inv := fun g => by cases g; rfl }

/-- Every complete-flag chain is exactly a partial gallery with an
independent full lift of each of its common-facet refinements. -/
def configurationEquiv {I J : Index n} (path : Chain I J)
    (source target : FullFlag k n) :
    FullGallery path source target ≃
      ((g : PolynomialFlags.Gallery path (forget I source) (forget J target)) × Decorations path g) := by
  induction path generalizing target with
  | nil =>
      let e : FullGallery (.nil I) source target ≃
          PolynomialFlags.Gallery (.nil I) (forget I source) (forget I target) :=
        Equiv.cast (by rw [FullGallery,PolynomialFlags.Gallery])
      refine e.trans ?_
      simp only [Decorations]
      exact {
        toFun := fun g => ⟨g,()⟩
        invFun := fun g => g.1
        left_inv := fun _ => rfl
        right_inv := fun g => by rcases g with ⟨g,⟨⟩⟩; rfl }
  | @snoc J path T ih =>
      simp only [FullGallery]
      let e : ((E : FullFlag k n) × FullGallery path source E ×
          PLift (forget T E = forget T target)) ≃
          ((E : FullFlag k n) ×
            ((g : PolynomialFlags.Gallery path (forget _ source) (forget J E)) ×
              Decorations path g) × PLift (forget T E = forget T target)) :=
        Equiv.sigmaCongrRight (fun E =>
          (ih E).prodCongr (Equiv.refl _))
      exact e.trans ((lastEquiv J T
        (fun F => (g : PolynomialFlags.Gallery path (forget _ source) F) × Decorations path g)
        (forget T target)).trans (reassocEquiv path T (forget _ source) (forget T target)))

instance fullGallery_finite [Finite k] {I J : Index n} (path : Chain I J)
    (source target : FullFlag k n) : Finite (FullGallery path source target) := by
  letI := PolynomialFlags.gallery_finite path (forget I source) (forget J target)
  exact Finite.of_injective (configurationEquiv path source target)
    (configurationEquiv path source target).injective

#print axioms lastEquiv
#print axioms configurationEquiv
#print axioms fullGallery_finite
end Guralnick.PolynomialFullGallery
