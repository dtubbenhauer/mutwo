import Guralnick.AffineGroup
import Guralnick.CanonicalMatrix
import Mathlib.Order.Interval.Finset.Fin

/-!
# The supported packet matrix of an actual affine permutation

Entries count output residues in the three actual row blocks whose inverse
winding has the specified value -1,0,1. Row margins and balance of the outer
columns are proved from residue partition and the affine sum condition.
-/
noncomputable section
namespace Guralnick.WindowPacketMatrix
open scoped BigOperators
open CanonicalMatrix

/-- Zero-based output residue blocks of sizes m,1,m. -/
def rowOf (m : ℕ) (i : Fin (2*m+1)) : Fin 3 :=
  if i.val < m then 0 else if i.val = m then 1 else 2

@[simp] theorem rowOf_zero (m : ℕ) (i : Fin (2*m+1)) : rowOf m i = 0 ↔ i.val < m := by
  unfold rowOf
  split_ifs <;> norm_num <;> omega

@[simp] theorem rowOf_one (m : ℕ) (i : Fin (2*m+1)) : rowOf m i = 1 ↔ i.val = m := by
  unfold rowOf
  split_ifs <;> norm_num <;> omega

@[simp] theorem rowOf_two (m : ℕ) (i : Fin (2*m+1)) : rowOf m i = 2 ↔ m < i.val := by
  unfold rowOf
  split_ifs <;> norm_num <;> omega

def entries (m : ℕ) (w : AffinePermutation (2*m+1)) (row col : Fin 3) : ℕ :=
  (Finset.univ.filter fun i : Fin (2*m+1) =>
    rowOf m i = row ∧ (w⁻¹).winding i = Family.columnShift col).card

def Supported {n : ℕ} (w : AffinePermutation n) : Prop :=
  ∀ i, -1 ≤ (w⁻¹).winding i ∧ (w⁻¹).winding i ≤ 1

theorem card_filter_sum {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ i : ι, if P i then 1 else 0 := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]

theorem card_filter_sum_int {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℤ) = ∑ i : ι, if P i then 1 else 0 := by
  rw [card_filter_sum]
  push_cast
  rfl

private theorem row_card (m : ℕ) (row : Fin 3) :
    (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = row).card =
      ![m,1,m] row := by
  fin_cases row
  · change (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = 0).card = m
    have he : (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = 0) =
        Finset.Iio (⟨m,by omega⟩ : Fin (2*m+1)) := by
      ext i
      simp [Finset.mem_Iio,Fin.lt_def]
    rw [he,Fin.card_Iio]
  · change (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = 1).card = 1
    have he : (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = 1) =
        {⟨m,by omega⟩} := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      rw [rowOf_one,Fin.ext_iff]
    rw [he]
    simp
  · change (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = 2).card = m
    have he : (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = 2) =
        Finset.Ioi (⟨m,by omega⟩ : Fin (2*m+1)) := by
      ext i
      simp [Finset.mem_Ioi,Fin.lt_def]
    rw [he,Fin.card_Ioi]
    simp
    omega

/-- Every output residue occurs in exactly one of the three supported columns. -/
theorem row_sum (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (row : Fin 3) : entries m w row 0 + entries m w row 1 + entries m w row 2 =
      ![m,1,m] row := by
  rw [← row_card m row]
  simp only [entries, card_filter_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hs i
  have hh : (w⁻¹).winding i = -1 ∨ (w⁻¹).winding i = 0 ∨ (w⁻¹).winding i = 1 := by omega
  rcases hh with hh | hh | hh <;>
    by_cases hr : rowOf m i = row <;> simp [Family.columnShift,hh,hr]

/-- Summing the three output blocks counts all residues with a given inverse winding. -/
theorem column_sum (m : ℕ) (w : AffinePermutation (2*m+1)) (col : Fin 3) :
    entries m w 0 col + entries m w 1 col + entries m w 2 col =
      (Finset.univ.filter fun i => (w⁻¹).winding i = Family.columnShift col).card := by
  simp only [entries,card_filter_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hw : (w⁻¹).winding i = Family.columnShift col
  · simp only [hw,and_true,ite_true]
    have hr : rowOf m i = 0 ∨ rowOf m i = 1 ∨ rowOf m i = 2 := by
      have h := (rowOf m i).isLt
      omega
    rcases hr with hr | hr | hr <;> simp [hr]
  · simp [hw]

/-- Zero total winding balances the positive and negative supported packets. -/
theorem balanced_packets (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    (Finset.univ.filter fun i => (w⁻¹).winding i = -1).card =
      (Finset.univ.filter fun i => (w⁻¹).winding i = 1).card := by
  have hsum : ∑ i, (w⁻¹).winding i =
      ((Finset.univ.filter fun i => (w⁻¹).winding i = 1).card : ℤ) -
      ((Finset.univ.filter fun i => (w⁻¹).winding i = -1).card : ℤ) := by
    rw [card_filter_sum_int,card_filter_sum_int,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := hs i
    split_ifs <;> omega
  rw [(w⁻¹).balanced] at hsum
  omega

/-- A genuine supported affine window supplies the numerical packet object;
none of its margins or balance conditions is assumed. -/
def packetMatrix (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) : PacketMatrix m where
  entries := entries m w
  first_row := row_sum m w hs 0
  middle_row := row_sum m w hs 1
  last_row := row_sum m w hs 2
  outer_columns := by
    rw [column_sum,column_sum]
    simpa [Family.columnShift] using balanced_packets m w hs

end Guralnick.WindowPacketMatrix
