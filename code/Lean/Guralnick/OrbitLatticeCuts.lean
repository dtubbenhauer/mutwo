import Guralnick.OrbitMatrix
import Guralnick.QuotientIntersections
import Guralnick.MainGalleryCount

/-! # Actual periodic cuts and quotient intersections

These are elementary identities of the explicitly defined Laurent lattices.
They connect the generic coordinate-dimension theorem with the quotient
subspaces used in the manuscript's finite gallery calculation.
-/
noncomputable section
namespace Guralnick.OrbitMatrix
open LaurentLattice AffineLatticePosition LatticeGallery
open LatticeFlags LatticeFlags.Family
open Classical
variable (k : Type*) [Field k] (N : ℕ) [NeZero N]

def scalarShift : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N :=
  LinearEquiv.smulOfNeZero (LaurentSeries k) (Ambient k N)
    (monomial k (-1)) (by simp [monomial])

theorem scalarShift_coordinateVector (i : Fin N) (q : ℤ) :
    scalarShift k N (coordinateVector k N i q) = coordinateVector k N i (q+1) := by
  funext j
  by_cases h : i = j
  · subst j
    simp only [scalarShift, LinearEquiv.smulOfNeZero_apply, coordinateVector,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    rw [monomial_mul]
    congr 1
    omega
  · simp [scalarShift, coordinateVector, h]

theorem mapModule_restrictScalars (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (A : Submodule (PowerSeries k) (Ambient k N)) :
    (mapModule k N g A).restrictScalars k =
      (A.restrictScalars k).map (g.restrictScalars k).toLinearMap := by
  rfl

theorem scalarShift_map (A : Submodule (PowerSeries k) (Ambient k N)) :
    (mapModule k N (scalarShift k N) A).restrictScalars k =
      expand (shift k N) (A.restrictScalars k) := by
  rfl

theorem scalarShift_commutes (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) :
    (scalarShift k N).trans g = g.trans (scalarShift k N) := by
  apply LinearEquiv.ext
  intro x
  exact g.map_smul _ _

theorem coordinateModule_period :
    coordinateModule k N N = mapModule k N (scalarShift k N) (coordinateModule k N 0) := by
  unfold coordinateModule mapModule
  rw [Submodule.map_span, ← Set.range_comp']
  congr 1
  apply congrArg Set.range
  funext i
  simp only [Nat.not_lt_zero, if_false, i.isLt, if_true]
  exact (scalarShift_coordinateVector k N i 0).symm

theorem targetCut_period (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) :
    targetCut k N g N = expand (shift k N) (targetCut k N g 0) := by
  unfold targetCut
  have hz : cutModule k N (0 : ℤ) = coordinateModule k N 0 := cutModule_nat k N 0 (Nat.zero_le N)
  rw [cutModule_nat k N N le_rfl, hz,
    coordinateModule_period, ← mapModule_trans, scalarShift_commutes,
    mapModule_trans, scalarShift_map]

theorem sourceCut_period (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) :
    sourceCut k N g w N = expand (shift k N) (sourceCut k N g w 0) :=
  targetCut_period k N ((windowEquiv k N w).trans g)

/-- The common basis in actual relative position gives precisely the cut
at every retained boundary vertex. -/
theorem relativePosition_cuts {S T : Finset (Fin N)}
    {target : Flag k N T} {source : Flag k N S} {w : AffinePermutation N}
    (h : RelativePosition k N target source w) :
    ∃ g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N,
      (∀ i, targetCut k N g i.val.val = (target.node i).space) ∧
      (∀ i, sourceCut k N g w i.val.val = (source.node i).space) := by
  obtain ⟨g,ht,hs⟩ := h
  refine ⟨g,?_,?_⟩
  · intro i
    unfold targetCut
    rw [cutModule_nat k N i.val.val (Nat.le_of_lt i.val.isLt),ht i]
    rfl
  · intro i
    unfold sourceCut
    rw [cutModule_nat k N i.val.val (Nat.le_of_lt i.val.isLt),hs i]
    rfl

/-- A single common Laurent basis at the four boundary cuts of the main
three-row corner. This is extracted from actual relative position. -/
structure MainCoordinates {m : ℕ} (hm : 2 ≤ m)
    (source : Flag k (2*m+1) (S m)) (target : Flag k (2*m+1) (O m))
    (w : AffinePermutation (2*m+1)) where
  basis : Ambient k (2*m+1) ≃ₗ[LaurentSeries k] Ambient k (2*m+1)
  zero : targetCut k (2*m+1) basis 0 = (targetNode target).space
  middle : targetCut k (2*m+1) basis m = (targetF target).space
  next : targetCut k (2*m+1) basis (m+1) = (targetF' hm target).space
  source : sourceCut k (2*m+1) basis w 0 = (sourceNode source).space

def mainCoordinates {m : ℕ} (hm : 2 ≤ m)
    {source : Flag k (2*m+1) (S m)} {target : Flag k (2*m+1) (O m)}
    {w : AffinePermutation (2*m+1)}
    (h : RelativePosition k (2*m+1) target source w) :
    MainCoordinates k hm source target w := by
  let g := Classical.choose (relativePosition_cuts k (2*m+1) h)
  have ht := (Classical.choose_spec (relativePosition_cuts k (2*m+1) h)).1
  have hs := (Classical.choose_spec (relativePosition_cuts k (2*m+1) h)).2
  exact ⟨g, ht ⟨⟨0,by omega⟩,(output_mem m _).mpr (Or.inl rfl)⟩,
    ht ⟨⟨m,by omega⟩,(output_mem m _).mpr (Or.inr (Or.inl rfl))⟩,
    ht ⟨⟨m+1,by omega⟩,(output_mem m _).mpr (Or.inr (Or.inr rfl))⟩,
    hs ⟨⟨0,by omega⟩,(source_mem m _).mpr rfl⟩⟩

end Guralnick.OrbitMatrix
