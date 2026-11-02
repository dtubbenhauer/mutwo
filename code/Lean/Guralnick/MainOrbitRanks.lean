import Guralnick.OrbitLatticeCuts

/-! # Actual quotient ranks from the periodic endpoint window

The six subspace dimensions used in the main gallery count are derived
from the ordinary periodic coordinate theorem. No rank formula particular
to the manuscript family is assumed as literature input.
-/
noncomputable section
namespace Guralnick.OrbitMatrix
open LaurentLattice AffineLatticePosition LatticeGallery
open LatticeFlags LatticeFlags.Family
open MainGalleryCount
variable {k : Type} [Field k] {m : ℕ} (hm : 2 ≤ m)
  {source : Flag k (2*m+1) (S m)} {target : Flag k (2*m+1) (O m)}
  {w : AffinePermutation (2*m+1)}
  (C : MainCoordinates k hm source target w)
  (h : Bounds source target)
  (input : CoordinateDimensionInput k (2*m+1))

theorem MainCoordinates.top :
    targetCut k (2*m+1) C.basis (2*m+1 : ℕ) = upper target := by
  rw [targetCut_period,C.zero]

theorem MainCoordinates.sourceTop :
    sourceCut k (2*m+1) C.basis w (2*m+1 : ℕ) =
      expand (shift k (2*m+1)) (sourceNode source).space := by
  rw [sourceCut_period,C.source]

/-- A one-period containment controls every winding of an actual window. -/
theorem winding_upper_of_cut_bound {N : ℕ} [NeZero N] (u : AffinePermutation N)
    (hu : ∀ z : ℤ, z ≤ 0 → u.onIntegers z ≤ N) (i : Fin N) :
    u.winding i ≤ 1 := by
  have hi := i.isLt
  have h := hu ((i.val : ℤ)+1+N*(-1)) (by omega)
  rw [onIntegers_packet] at h
  unfold AffinePermutation.entry at h
  have hp : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  have hr : (0 : ℤ) ≤ (u.residue i).val := by positivity
  by_contra hn
  have hw : 2 ≤ u.winding i := by omega
  nlinarith

/-- Conversely, an upper bound on every winding gives the actual
one-period integer containment. -/
theorem cut_bound_of_winding_upper {N : ℕ} [NeZero N] (u : AffinePermutation N)
    (hu : ∀ i, u.winding i ≤ 1) (z : ℤ) (hz : z ≤ 0) : u.onIntegers z ≤ N := by
  obtain ⟨⟨i,q⟩,rfl⟩ := (AffinePermutation.integerIndex N).surjective z
  rw [AffinePermutation.integerIndex_apply] at hz
  rw [AffinePermutation.onIntegers_index,AffinePermutation.integerIndex_apply]
  change ((u.residue i).val : ℤ)+1+N*(q+u.winding i) ≤ N
  have hp : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  have hi := i.isLt
  have hir := (u.residue i).isLt
  have hq : q ≤ -1 := by
    by_contra hn
    have hqn : 0 ≤ q := by omega
    have hi0 : (0 : ℤ) ≤ i.val := by positivity
    nlinarith
  have hw := hu i
  have hmul : (N : ℤ)*(q+u.winding i) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  omega

include C input

/-- The window support condition also implies the genuine endpoint
containments, in every realization of that relative position. -/
def MainCoordinates.bounds_of_inverse_winding
    (hs : ∀ i, -1 ≤ (w⁻¹).winding i ∧ (w⁻¹).winding i ≤ 1) :
    Bounds source target := by
  have hw : ∀ i, w.winding i ≤ 1 := by
    intro i
    have ht := (hs (w.residue i)).1
    change -1 ≤ -w.winding (w.residue.symm (w.residue i)) at ht
    rw [Equiv.symm_apply_apply] at ht
    omega
  constructor
  · change (sourceNode source).space ≤ upper target
    rw [← C.source,← C.top hm]
    apply (input.source_le_target C.basis w (2*m+1 : ℕ) 0).mpr
    exact cut_bound_of_winding_upper w hw
  · rw [← C.zero,← C.sourceTop hm]
    apply (input.target_le_source C.basis w 0 (2*m+1 : ℕ)).mpr
    rw [← onIntegers_inv]
    exact cut_bound_of_winding_upper (w⁻¹) (fun i => (hs i).2)

include h

/-- The two endpoint containments forced by the web prove the support
restriction on the inverse window; it is not a family-specific input. -/
theorem bounds_inverse_winding (i : Fin (2*m+1)) :
    -1 ≤ (w⁻¹).winding i ∧ (w⁻¹).winding i ≤ 1 := by
  have hw : ∀ z : ℤ, z ≤ 0 → w.onIntegers z ≤ (2*m+1 : ℕ) := by
    apply (input.source_le_target C.basis w (2*m+1 : ℕ) 0).mp
    rw [C.source,C.top hm]
    exact h.source_le
  have hwi : ∀ z : ℤ, z ≤ 0 → (w⁻¹).onIntegers z ≤ (2*m+1 : ℕ) := by
    rw [onIntegers_inv]
    apply (input.target_le_source C.basis w 0 (2*m+1 : ℕ)).mp
    rw [C.zero,C.sourceTop hm]
    exact h.target_le
  constructor
  · have hneg := winding_upper_of_cut_bound w hw (w.residue.symm i)
    change -1 ≤ -w.winding (w.residue.symm i)
    omega
  · exact winding_upper_of_cut_bound (w⁻¹) hwi i

theorem lower_rank_cumulative :
    Module.finrank k (lower h) = cumulativeCount (2*m+1) w 0 (2*m+1 : ℕ) 0 := by
  change Module.finrank k (quotientImage (base target) (upper target) _
    (I0 h).val (I0 h).property.1 (I0 h).property.2) = _
  rw [quotientImage_finrank]
  have hd := input.cumulative_dimension C.basis w 0 (2*m+1 : ℕ) 0 (by omega)
  unfold CumulativeQuotient at hd
  rw [C.zero,C.top hm,C.source] at hd
  change Module.finrank k (QuotientSpace (base target) (upper target ⊓ (I0 h).val)) = _ at hd
  rw [inf_eq_right.mpr (I0 h).property.2] at hd
  exact hd

theorem upper_rank_cumulative :
    Module.finrank k (upperFlag h) =
      cumulativeCount (2*m+1) w 0 (2*m+1 : ℕ) (2*m+1 : ℕ) := by
  change Module.finrank k (quotientImage (base target) (upper target) _
    (K0 h).val (K0 h).property.1 (K0 h).property.2) = _
  rw [quotientImage_finrank]
  have hd := input.cumulative_dimension C.basis w 0 (2*m+1 : ℕ) (2*m+1 : ℕ) (by omega)
  unfold CumulativeQuotient at hd
  rw [C.zero,C.top hm,C.sourceTop hm,sup_eq_left.mpr h.target_le,inf_comm] at hd
  exact hd

/-- Intersection with an arbitrary retained target cut, covering both
middle vertices m and m+1 without duplicating the lattice argument. -/
theorem lower_intersection_rank_cumulative
    (A : Set.Icc (base target) (upper target)) (b : ℕ) (hb : b ≤ 2*m+1)
    (hA : targetCut k (2*m+1) C.basis b = A.val) :
    Module.finrank k ((quotientOrder target).symm (I0 h) ⊓
      (quotientOrder target).symm A : Submodule k (Space target)) =
      cumulativeCount (2*m+1) w 0 b 0 := by
  unfold quotientOrder
  rw [quotientImage_inf_finrank]
  have hd := input.cumulative_dimension C.basis w 0 b 0 (by omega)
  unfold CumulativeQuotient at hd
  rw [C.zero,C.source,hA,inf_comm] at hd
  exact hd

theorem upper_intersection_rank_cumulative
    (A : Set.Icc (base target) (upper target)) (b : ℕ) (hb : b ≤ 2*m+1)
    (hA : targetCut k (2*m+1) C.basis b = A.val) :
    Module.finrank k ((quotientOrder target).symm (K0 h) ⊓
      (quotientOrder target).symm A : Submodule k (Space target)) =
      cumulativeCount (2*m+1) w 0 b (2*m+1 : ℕ) := by
  unfold quotientOrder
  rw [quotientImage_inf_finrank]
  have hd := input.cumulative_dimension C.basis w 0 b (2*m+1 : ℕ) (by omega)
  unfold CumulativeQuotient at hd
  rw [C.zero,C.sourceTop hm,hA,sup_eq_left.mpr h.target_le,inf_comm] at hd
  change Module.finrank k (QuotientSpace (base target)
    ((expand (shift k (2*m+1)) (sourceNode source).space ⊓ upper target) ⊓ A.val)) = _
  rw [inf_assoc,inf_eq_right.mpr A.property.2]
  exact hd

end Guralnick.OrbitMatrix
