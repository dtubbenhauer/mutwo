import Guralnick.RelativeDimensions
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Quotients of coordinate subspaces

For an actual basis, intersection and sum correspond to intersection and
union of index sets. The relative quotient keeps exactly the coordinates
in the upper set which do not belong to the lower set. Its dimension is
therefore a proved cardinality, with no coordinate-counting input.
-/
noncomputable section
namespace Guralnick.CoordinateSubspace
variable {k ι V : Type*} [Field k] [AddCommGroup V] [Module k V]

def spanSet (e : Basis ι k V) (S : Set ι) : Submodule k V :=
  Submodule.span k (e '' S)

theorem mem_spanSet (e : Basis ι k V) (S : Set ι) (x : V) :
    x ∈ spanSet e S ↔ e.repr x ∈ Finsupp.supported k k S :=
  e.mem_span_image

theorem spanSet_inf (e : Basis ι k V) (A B : Set ι) :
    spanSet e A ⊓ spanSet e B = spanSet e (A ∩ B) := by
  ext x
  simp only [Submodule.mem_inf,mem_spanSet, Finsupp.supported_inter]

theorem spanSet_sup (e : Basis ι k V) (A B : Set ι) :
    spanSet e A ⊔ spanSet e B = spanSet e (A ∪ B) := by
  simp only [spanSet,Set.image_union,Submodule.span_union]

theorem spanSet_le_iff (e : Basis ι k V) (A B : Set ι) :
    spanSet e A ≤ spanSet e B ↔ A ⊆ B := by
  classical
  constructor
  · intro h i hi
    have hm : e i ∈ spanSet e B := h (Submodule.subset_span ⟨i,hi,rfl⟩)
    have hs := (mem_spanSet e B (e i)).mp hm
    apply hs
    simp
  · intro h
    exact Submodule.span_mono (Set.image_mono h)

def reprEquiv (e : Basis ι k V) (S : Set ι) :
    spanSet e S ≃ₗ[k] Finsupp.supported k k S where
  toFun x := ⟨e.repr x.val,(mem_spanSet e S x.val).mp x.property⟩
  invFun f := ⟨e.repr.symm f.val,by
    rw [mem_spanSet,e.repr.apply_symm_apply]
    exact f.property⟩
  left_inv x := Subtype.ext (e.repr.symm_apply_apply x.val)
  right_inv f := Subtype.ext (e.repr.apply_symm_apply f.val)
  map_add' x y := Subtype.ext (e.repr.map_add x.val y.val)
  map_smul' a x := Subtype.ext (e.repr.map_smul a x.val)

def projection (A B : Set ι) :
    Finsupp.supported k k B →ₗ[k] Finsupp.supported k k (B \ A) := by
  classical
  exact (Finsupp.restrictDom k k (B \ A)).comp (Finsupp.supported k k B).subtype

theorem projection_kernel (A B : Set ι) :
    LinearMap.ker (projection (k := k) A B) =
      (Finsupp.supported k k A).comap (Finsupp.supported k k B).subtype := by
  classical
  ext f
  change projection A B f = 0 ↔ f.val ∈ Finsupp.supported k k A
  rw [Finsupp.mem_supported']
  constructor
  · intro h i hi
    by_cases hib : i ∈ B
    · have he := congrArg (fun g : Finsupp.supported k k (B \ A) => g.val i) h
      simpa [projection,hib,hi] using he
    · exact (Finsupp.mem_supported' k f.val).mp f.property i hib
  · intro h
    apply Subtype.ext
    ext i
    change (Finsupp.filter (· ∈ B \ A) f.val) i = 0
    by_cases hi : i ∈ B \ A
    · rw [Finsupp.filter_apply,if_pos hi]
      exact h i hi.2
    · rw [Finsupp.filter_apply,if_neg hi]

theorem projection_surjective (A B : Set ι) :
    Function.Surjective (projection (k := k) A B) := by
  classical
  intro f
  refine ⟨⟨f.val,Finsupp.supported_mono Set.diff_subset f.property⟩,?_⟩
  apply Subtype.ext
  ext i
  change (Finsupp.filter (· ∈ B \ A) f.val) i = f.val i
  by_cases hi : i ∈ B \ A
  · rw [Finsupp.filter_apply,if_pos hi]
  · have hz := (Finsupp.mem_supported' k f.val).mp f.property i hi
    rw [Finsupp.filter_apply,if_neg hi,hz]

def supportedQuotientEquiv (A B : Set ι) :
    LatticeGallery.QuotientSpace (Finsupp.supported k k A) (Finsupp.supported k k B)
      ≃ₗ[k] Finsupp.supported k k (B \ A) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel A B).symm).trans
    ((projection A B).quotKerEquivOfSurjective (projection_surjective A B))

theorem reprEquiv_lower (e : Basis ι k V) (A B : Set ι) :
    ((spanSet e A).comap (spanSet e B).subtype).map (reprEquiv e B).toLinearMap =
      (Finsupp.supported k k A).comap (Finsupp.supported k k B).subtype := by
  ext f
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (mem_spanSet e A x.val).mp hx
  · intro hf
    refine ⟨(reprEquiv e B).symm f,?_,(reprEquiv e B).apply_symm_apply f⟩
    change e.repr.symm f.val ∈ spanSet e A
    rw [mem_spanSet,e.repr.apply_symm_apply]
    exact hf

/-- The actual quotient is the vector space on the surviving basis indices. -/
def quotientEquiv (e : Basis ι k V) (A B : Set ι) :
    LatticeGallery.QuotientSpace (spanSet e A) (spanSet e B) ≃ₗ[k]
      (↥(B \ A) →₀ k) :=
  (Submodule.Quotient.equiv _ _ (reprEquiv e B) (reprEquiv_lower e A B)).trans
    ((supportedQuotientEquiv A B).trans (Finsupp.supportedEquivFinsupp (B \ A)))

theorem quotient_finrank (e : Basis ι k V) (A B : Set ι) (s : Finset ι)
    (hs : B \ A = (s : Set ι)) :
    Module.finrank k (LatticeGallery.QuotientSpace (spanSet e A) (spanSet e B)) = s.card := by
  classical
  letI : Fintype ↥(B \ A) := Fintype.ofEquiv (s : Set ι) (Equiv.setCongr hs).symm
  rw [(quotientEquiv e A B).finrank_eq,Module.finrank_finsupp_self]
  exact (Fintype.card_congr (Equiv.setCongr hs)).trans (Fintype.card_coe s)

#print axioms quotientEquiv
#print axioms quotient_finrank
end Guralnick.CoordinateSubspace
