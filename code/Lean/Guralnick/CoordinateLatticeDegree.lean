import Guralnick.AffineLatticePosition
import Guralnick.LatticeDegree

/-!
# The absolute degree of the actual coordinate lattice

The first `a` coordinates are enlarged by one power of t. Their residues
identify the actual quotient by the standard lattice with k^a. This fixes
the absolute degree used in canonical flag endpoints without a literature
or orbit-coordinate assumption.
-/
noncomputable section
namespace Guralnick.AffineLatticePosition
open LaurentLattice
open scoped BigOperators
variable (k : Type*) [Field k] (N : ℕ)

def coordinateEmbedding (a : ℕ) :
    (Fin N → PowerSeries k) →ₗ[PowerSeries k] Ambient k N where
  toFun f i := monomial k (-(if i.val < a then 1 else 0)) *
    algebraMap (PowerSeries k) (LaurentSeries k) (f i)
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by
    funext i
    change _ * algebraMap (PowerSeries k) (LaurentSeries k) (c * f i) =
      algebraMap (PowerSeries k) (LaurentSeries k) c * (_ * _)
    rw [map_mul]
    ring

theorem coordinateEmbedding_single (a : ℕ) (i : Fin N) :
    coordinateEmbedding k N a (Pi.single i 1) =
      coordinateVector k N i (if i.val < a then 1 else 0) := by
  classical
  ext j
  by_cases h : i = j
  · subst j; simp [coordinateEmbedding,coordinateVector]
  · simp [coordinateEmbedding,coordinateVector,h]

theorem coordinateEmbedding_range (a : ℕ) :
    LinearMap.range (coordinateEmbedding k N a) = coordinateModule k N a := by
  classical
  apply le_antisymm
  · rintro x ⟨f,rfl⟩
    rw [← Finset.univ_sum_single f,map_sum]
    apply Submodule.sum_mem
    intro i _
    have he : (Pi.single i (f i) : Fin N → PowerSeries k) =
        (f i) • (Pi.single i 1 : Fin N → PowerSeries k) := by
      funext j
      by_cases hij : i = j
      · subst j; simp
      · simp [Pi.smul_apply,hij]
    rw [he,map_smul,coordinateEmbedding_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact ⟨Pi.single i 1,coordinateEmbedding_single k N a i⟩

theorem coordinateEmbedding_injective (a : ℕ) :
    Function.Injective (coordinateEmbedding k N a) := by
  intro f g h
  funext i
  have hi := congrFun h i
  change monomial k _ * _ = monomial k _ * _ at hi
  apply IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
  exact mul_left_cancel₀ (by simp [monomial]) hi

def coordinateParameters (a : ℕ) :
    (Fin N → PowerSeries k) ≃ₗ[PowerSeries k] coordinateModule k N a :=
  LinearEquiv.ofBijective
    ((coordinateEmbedding k N a).codRestrict (coordinateModule k N a)
      (fun f => coordinateEmbedding_range k N a ▸ LinearMap.mem_range_self _ f)) (by
        constructor
        · intro f g h
          exact coordinateEmbedding_injective k N a (congrArg Subtype.val h)
        · intro x
          have hx : x.val ∈ LinearMap.range (coordinateEmbedding k N a) := by
            rw [coordinateEmbedding_range]
            exact x.property
          obtain ⟨f,hf⟩ := hx
          exact ⟨f,Subtype.ext hf⟩)

@[simp] theorem coordinateParameters_val (a : ℕ) (f : Fin N → PowerSeries k) :
    (coordinateParameters k N a f).val = coordinateEmbedding k N a f := rfl

theorem monomial_neg_one_mul_powerSeries (f g : PowerSeries k) :
    monomial k (-1) * algebraMap (PowerSeries k) (LaurentSeries k) f =
      algebraMap (PowerSeries k) (LaurentSeries k) g ↔ f = PowerSeries.X * g := by
  have hx : algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X = monomial k 1 := by
    exact HahnSeries.ofPowerSeries_X
  constructor
  · intro h
    apply IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
    rw [map_mul,hx,← h,← mul_assoc,monomial_mul]
    simp
  · intro h
    rw [h,map_mul,hx,← mul_assoc,monomial_mul]
    simp

theorem coordinateEmbedding_mem_standard_iff (a : ℕ) (f : Fin N → PowerSeries k) :
    coordinateEmbedding k N a f ∈ standardModule k N ↔
      ∀ i : Fin N, i.val < a → PowerSeries.constantCoeff k (f i) = 0 := by
  classical
  constructor
  · rintro ⟨g,hg⟩ i hi
    have he := (congrFun hg i).symm
    change monomial k (-(if i.val < a then 1 else 0)) * _ = _ at he
    rw [if_pos hi] at he
    have hf := (monomial_neg_one_mul_powerSeries k (f i) (g i)).mp he
    rw [hf,map_mul,PowerSeries.constantCoeff_X,zero_mul]
  · intro h
    have hex : ∀ i : Fin N, ∃ g : PowerSeries k,
        monomial k (-(if i.val < a then 1 else 0)) *
          algebraMap (PowerSeries k) (LaurentSeries k) (f i) =
          algebraMap (PowerSeries k) (LaurentSeries k) g := by
      intro i
      by_cases hi : i.val < a
      · obtain ⟨g,hg⟩ := PowerSeries.X_dvd_iff.mpr (h i hi)
        refine ⟨g,?_⟩
        rw [if_pos hi]
        exact (monomial_neg_one_mul_powerSeries k (f i) g).mpr hg
      · exact ⟨f i,by simp [hi]⟩
    choose g hg using hex
    exact ⟨g,funext fun i => (hg i).symm⟩

def firstConstants (a : ℕ) (ha : a ≤ N) :
    (Fin N → PowerSeries k) →ₗ[k] (Fin a → k) where
  toFun f i := PowerSeries.constantCoeff k (f ⟨i.val,lt_of_lt_of_le i.isLt ha⟩)
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp [PowerSeries.constantCoeff_smul]

def coordinateResidues (a : ℕ) (ha : a ≤ N) :
    (coordinateLattice k N a).space →ₗ[k] (Fin a → k) :=
  (firstConstants k N a ha).comp
    ((coordinateParameters k N a).symm.restrictScalars k).toLinearMap

theorem coordinateResidues_surjective (a : ℕ) (ha : a ≤ N) :
    Function.Surjective (coordinateResidues k N a ha) := by
  classical
  intro f
  let g : Fin N → PowerSeries k := fun i =>
    if hi : i.val < a then PowerSeries.C k (f ⟨i.val,hi⟩) else 0
  refine ⟨coordinateParameters k N a g,?_⟩
  change firstConstants k N a ha
    ((coordinateParameters k N a).symm (coordinateParameters k N a g)) = f
  rw [LinearEquiv.symm_apply_apply]
  funext i
  simp [firstConstants,g,i.isLt]

theorem coordinateResidues_kernel (a : ℕ) (ha : a ≤ N) :
    LinearMap.ker (coordinateResidues k N a ha) =
      ((standardLattice k N).space).comap (coordinateLattice k N a).space.subtype := by
  ext x
  let f := (coordinateParameters k N a).symm x
  have hx : coordinateEmbedding k N a f = x.val :=
    congrArg Subtype.val ((coordinateParameters k N a).apply_symm_apply x)
  change coordinateResidues k N a ha x = 0 ↔ x.val ∈ standardModule k N
  rw [← hx,coordinateEmbedding_mem_standard_iff]
  constructor
  · intro h i hi
    exact congrFun h ⟨i.val,hi⟩
  · intro h
    funext i
    exact h ⟨i.val,lt_of_lt_of_le i.isLt ha⟩ i.isLt

def coordinateQuotientEquiv (a : ℕ) (ha : a ≤ N) :
    LatticeGallery.QuotientSpace (standardLattice k N).space
      (coordinateLattice k N a).space ≃ₗ[k] (Fin a → k) :=
  (Submodule.quotEquivOfEq _ _ (coordinateResidues_kernel k N a ha).symm).trans
    ((coordinateResidues k N a ha).quotKerEquivOfSurjective
      (coordinateResidues_surjective k N a ha))

theorem standard_le_coordinate (a : ℕ) : standardLattice k N ≤ coordinateLattice k N a := by
  classical
  change standardModule k N ≤ coordinateModule k N a
  rw [← coordinateModule_zero]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  simp only [Nat.not_lt_zero,if_false]
  by_cases hi : i.val < a
  · have h := (coordinateModule k N a).smul_mem (PowerSeries.X : PowerSeries k)
      (Submodule.subset_span ⟨i,rfl⟩)
    have he : (PowerSeries.X : PowerSeries k) •
        coordinateVector k N i (if i.val < a then 1 else 0) = coordinateVector k N i 0 := by
      funext j
      by_cases hij : i = j
      · subst j
        simp only [hi,if_true,coordinateVector,Pi.smul_apply,Pi.single_eq_same,
          Algebra.smul_def]
        rw [show algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X =
          monomial k 1 from HahnSeries.ofPowerSeries_X,monomial_mul]
        congr 1
      · simp [coordinateVector,hij]
    rwa [he] at h
  · exact Submodule.subset_span ⟨i,by simp [hi]⟩

@[simp] theorem standardLattice_degree : degree k N (standardLattice k N) = 0 := by
  simp [degree,standardLattice,Lattice.space]

theorem coordinateLattice_degree (a : ℕ) (ha : a ≤ N) :
    degree k N (coordinateLattice k N a) = (a : ℤ) := by
  have hd := dimension_degree (standardLattice k N) (coordinateLattice k N a)
    (standard_le_coordinate k N a)
  rw [standardLattice_degree,sub_zero] at hd
  have he := (coordinateQuotientEquiv k N a ha).finrank_eq
  simpa using hd.symm.trans (congrArg (fun n : ℕ => (n : ℤ)) he)

#print axioms coordinateQuotientEquiv
#print axioms coordinateLattice_degree
end Guralnick.AffineLatticePosition
