import Guralnick.PacketIndexClassification
import Guralnick.FiniteAuxiliaryBlocks

/-!
# Coarsening the actual strong and weak packet positions

Merging adjacent rows normally increases the periodic orbit dimension by
an explicit nonnegative crossing term. The two one-line support types have
zero crossing term. Their actual affine index therefore remains maximal
for the coarser output parabolic, by the general dimension criterion.
-/
noncomputable section
set_option maxHeartbeats 1200000
namespace Guralnick.PacketCoarsening
open scoped BigOperators
open Classical WindowPacketMatrix CanonicalMatrix

/-- Merge the final two output packets, preserving every winding column. -/
def mergeLast {R : Type*} [Add R] (A : Fin 3 → Fin 3 → R) : Fin 2 → Fin 3 → R :=
  ![A 0,fun j => A 1 j + A 2 j]

/-- Merge the initial two output packets, preserving every winding column. -/
def mergeFirst {R : Type*} [Add R] (A : Fin 3 → Fin 3 → R) : Fin 2 → Fin 3 → R :=
  ![fun j => A 0 j + A 1 j,A 2]

theorem dimension_two (A : Fin 2 → Fin 3 → ℤ) :
    PeriodicMatrix.dimension A =
      (A 0 0+A 1 0)*(A 0 2+A 1 2) +
      A 0 0*(A 0 1+A 0 2)+A 0 1*A 0 2 +
      A 1 0*(A 0 1+A 0 2+A 1 1+A 1 2)+A 1 1*(A 0 2+A 1 2) := by
  simp only [PeriodicMatrix.dimension,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ]
  norm_num
  ring

theorem dimension_mergeLast (A : Fin 3 → Fin 3 → ℤ) :
    PeriodicMatrix.dimension (mergeLast A) = PeriodicMatrix.dimension A +
      A 1 0*(A 2 1+A 2 2)+A 1 1*A 2 2 := by
  rw [dimension_two,PeriodicMatrix.dimension_three]
  simp only [mergeLast,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem dimension_mergeFirst (A : Fin 3 → Fin 3 → ℤ) :
    PeriodicMatrix.dimension (mergeFirst A) = PeriodicMatrix.dimension A +
      A 0 0*(A 1 1+A 1 2)+A 0 1*A 1 2 := by
  rw [dimension_two,PeriodicMatrix.dimension_three]
  simp only [mergeFirst,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- Actual interval counts at the coarse boundary m. -/
theorem compositionEntries_mergeLast {m : ℕ} (hm : 2 ≤ m)
    (w : AffinePermutation (2*m+1)) :
    OrbitMatrix.compositionEntries
      (FiniteAuxiliaryBlocks.two ⟨m,by omega⟩ (by dsimp; omega)) w =
      mergeLast (entries m w) := by
  funext row col
  change Fin 2 at row
  fin_cases row
  · change (Finset.univ.filter fun i : Fin (2*m+1) =>
        0 ≤ i.val ∧ i.val < m ∧ (w⁻¹).winding i = Family.columnShift col).card =
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        rowOf m i = 0 ∧ (w⁻¹).winding i = Family.columnShift col).card
    congr 1
    ext i
    simp
  · change (Finset.univ.filter fun i : Fin (2*m+1) =>
        m ≤ i.val ∧ i.val < m+(2*m+1-m) ∧ (w⁻¹).winding i = Family.columnShift col).card =
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        rowOf m i = 1 ∧ (w⁻¹).winding i = Family.columnShift col).card +
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        rowOf m i = 2 ∧ (w⁻¹).winding i = Family.columnShift col).card
    rw [card_filter_sum,card_filter_sum,card_filter_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    simp only [rowOf_one,rowOf_two]
    by_cases h : (w⁻¹).winding i = Family.columnShift col <;>
      simp [h] <;> split_ifs <;> omega

/-- Actual interval counts at the coarse boundary m+1. -/
theorem compositionEntries_mergeFirst {m : ℕ} (hm : 2 ≤ m)
    (w : AffinePermutation (2*m+1)) :
    OrbitMatrix.compositionEntries
      (FiniteAuxiliaryBlocks.two ⟨m+1,by omega⟩ (by dsimp; omega)) w =
      mergeFirst (entries m w) := by
  funext row col
  change Fin 2 at row
  fin_cases row
  · change (Finset.univ.filter fun i : Fin (2*m+1) =>
        0 ≤ i.val ∧ i.val < m+1 ∧ (w⁻¹).winding i = Family.columnShift col).card =
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        rowOf m i = 0 ∧ (w⁻¹).winding i = Family.columnShift col).card +
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        rowOf m i = 1 ∧ (w⁻¹).winding i = Family.columnShift col).card
    rw [card_filter_sum,card_filter_sum,card_filter_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [rowOf_zero,rowOf_one]
    by_cases h : (w⁻¹).winding i = Family.columnShift col <;>
      simp [h] <;> split_ifs <;> omega
  · change (Finset.univ.filter fun i : Fin (2*m+1) =>
        m+1 ≤ i.val ∧ i.val < m+1+(2*m+1-(m+1)) ∧
          (w⁻¹).winding i = Family.columnShift col).card =
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        rowOf m i = 2 ∧ (w⁻¹).winding i = Family.columnShift col).card
    congr 1
    ext i
    have hi := i.isLt
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,rowOf_two]
    omega

/-- The strong one-line positions have no new crossings when the last two
rows are merged. -/
theorem strong_dimension {m : ℕ} (A : PacketMatrix m)
    (hb : A.beta = 0) (hs : A.s = 0) :
    PeriodicMatrix.dimension (mergeLast (fun i j => (A.entries i j : ℤ))) =
      PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)) := by
  have h10 : (A.entries 1 0 : ℤ) = 0 := hb
  have h22 : (A.entries 2 2 : ℤ) = 0 := by unfold PacketMatrix.s at hs; omega
  rw [dimension_mergeLast,h10,h22]
  ring

/-- A weak one-line position has its singleton in column -1, so merging
its first two rows creates no new crossings. -/
theorem weak_dimension {m : ℕ} (A : PacketMatrix m) (hb : A.beta = 1) :
    PeriodicMatrix.dimension (mergeFirst (fun i j => (A.entries i j : ℤ))) =
      PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)) := by
  have hmid := A.middle_row
  have h11 : (A.entries 1 1 : ℤ) = 0 := by unfold PacketMatrix.beta at hb; omega
  have h12 : (A.entries 1 2 : ℤ) = 0 := by unfold PacketMatrix.beta at hb; omega
  rw [dimension_mergeFirst,h11,h12]
  ring

/-- The actual strong index is maximal at the two-row boundary (m,m+1). -/
theorem strong_doubleMaximal {m : ℕ} (hm : 2 ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) (O : OrbitMatrix.ThreeColumnLengthInput c)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output m)
      (ParabolicWeb.Family.source m) w)
    (hb : (packetMatrix m w hw).beta = 0) (hs : (packetMatrix m w hw).s = 0) :
    CanonicalSchur.DoubleMaximal c
      (CanonicalChains.twoRow (by omega) ⟨m,by omega⟩)
      (ParabolicWeb.Family.source m) w := by
  have hf := O.dimension_length (FiniteBlocks.Family.output hm) rfl w hw
    (by simpa only [FiniteBlocks.Family.output_index,
      ← FiniteBlocks.Family.source_eq_standard] using hmax)
  have hc := O.maximal_of_dimension
    (FiniteAuxiliaryBlocks.two ⟨m,by omega⟩ (by dsimp; omega)) rfl w hw
    (by simpa only [← FiniteBlocks.Family.source_eq_standard] using hmax.2)
  apply (by simpa only [FiniteAuxiliaryBlocks.two_index,
    ← FiniteBlocks.Family.source_eq_standard] using hc)
  rw [← hf]
  simp_rw [OrbitMatrix.compositionEntries_output]
  rw [compositionEntries_mergeLast hm]
  have he : (fun i j => ((mergeLast (entries m w) i j : ℕ) : ℤ)) =
      mergeLast (fun i j => (entries m w i j : ℤ)) := by
    funext i j
    fin_cases i <;> simp [mergeLast]
  change PeriodicMatrix.dimension (fun i j => (entries m w i j : ℤ)) =
    PeriodicMatrix.dimension (fun (i : Fin 2) j => ((mergeLast (entries m w) i j : ℕ) : ℤ))
  rw [he]
  exact (strong_dimension (packetMatrix m w hw) hb hs).symm

/-- The actual weak index is maximal at the two-row boundary (m+1,m). -/
theorem weak_doubleMaximal {m : ℕ} (hm : 2 ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) (O : OrbitMatrix.ThreeColumnLengthInput c)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output m)
      (ParabolicWeb.Family.source m) w)
    (hb : (packetMatrix m w hw).beta = 1) :
    CanonicalSchur.DoubleMaximal c
      (CanonicalChains.twoRow (by omega) ⟨m+1,by omega⟩)
      (ParabolicWeb.Family.source m) w := by
  have hf := O.dimension_length (FiniteBlocks.Family.output hm) rfl w hw
    (by simpa only [FiniteBlocks.Family.output_index,
      ← FiniteBlocks.Family.source_eq_standard] using hmax)
  have hc := O.maximal_of_dimension
    (FiniteAuxiliaryBlocks.two ⟨m+1,by omega⟩ (by dsimp; omega)) rfl w hw
    (by simpa only [← FiniteBlocks.Family.source_eq_standard] using hmax.2)
  apply (by simpa only [FiniteAuxiliaryBlocks.two_index,
    ← FiniteBlocks.Family.source_eq_standard] using hc)
  rw [← hf]
  simp_rw [OrbitMatrix.compositionEntries_output]
  rw [compositionEntries_mergeFirst hm]
  have he : (fun i j => ((mergeFirst (entries m w) i j : ℕ) : ℤ)) =
      mergeFirst (fun i j => (entries m w i j : ℤ)) := by
    funext i j
    fin_cases i <;> simp [mergeFirst]
  change PeriodicMatrix.dimension (fun i j => (entries m w i j : ℤ)) =
    PeriodicMatrix.dimension (fun (i : Fin 2) j => ((mergeFirst (entries m w) i j : ℕ) : ℤ))
  rw [he]
  exact (weak_dimension (packetMatrix m w hw) hb).symm

end Guralnick.PacketCoarsening
