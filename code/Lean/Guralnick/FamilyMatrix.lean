import Guralnick.Family

/-!
# The periodic matrix of the explicit affine family

The entries are counted from the actual translated images of the source block.
The prescribed matrix is not assumed or used to define those counts.
-/

namespace Guralnick.Family

/-- The number of integers in an interval, counted in an initial segment. -/
theorem range_filter_interval (n a b : ℕ) (hab : a ≤ b) :
    ((List.range n).filter fun i => decide (a ≤ i ∧ i < b)).length =
      min n b - min n a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : a ≤ n ∧ n < b
    · simp [h]
      omega
    · simp [h]
      omega

/-- Rearranging the window does not change block-intersection counts. -/
theorem matrixEntry_original {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (row : Fin 3) (shift : ℤ) :
    matrixEntry m (affine hm hj hjm) row shift =
      ((List.range (2*m+1)).filter fun a => inRow m row
        (((a+1 : ℕ) : ℤ) + (2*m+1 : ℕ) * familyShift m j (a+1) +
          (2*m+1 : ℕ)*shift)).length := by
  unfold matrixEntry
  rw [((window_perm_original hm hj hjm).filter _).length_eq, originalList_eq]
  rw [List.filter_map, List.length_map]
  rfl

/-- Interval endpoints for the nine relevant intersections, with zero-based
source residues. These intervals are derived from the defining shift rule. -/
def matrixInterval (m j : ℕ) (row col : Fin 3) : ℕ × ℕ :=
  match row.val, col.val with
  | 0, 0 => (m-1,m)
  | 0, 1 => (j-1,m-1)
  | 0, _ => (0,j-1)
  | 1, 0 => (0,0)
  | 1, 1 => (m,m+1)
  | 1, _ => (0,0)
  | _, 0 => (2*m+2-j,2*m+1)
  | _, 1 => (m+2,2*m+2-j)
  | _, _ => (m+1,m+2)

/-- The three columns are the source translates -1, 0 and +1. -/
def columnShift (col : Fin 3) : ℤ := (col.val : ℤ) - 1

set_option maxHeartbeats 1000000 in
theorem original_inRow_iff {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (row col : Fin 3) (a : ℕ) (ha : a < 2*m+1) :
    inRow m row (((a+1 : ℕ) : ℤ) + (2*m+1 : ℕ)*familyShift m j (a+1) +
      (2*m+1 : ℕ)*columnShift col) =
      decide ((matrixInterval m j row col).1 ≤ a ∧
        a < (matrixInterval m j row col).2) := by
  fin_cases row <;> fin_cases col <;>
    norm_num [inRow, matrixInterval, columnShift] <;>
    unfold familyShift <;> split_ifs <;>
    norm_num <;>
    first
    | omega
    | apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

/-- Every listed interval lies inside the source residue block. -/
theorem matrixInterval_bounds {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (row col : Fin 3) :
    (matrixInterval m j row col).1 ≤ (matrixInterval m j row col).2 ∧
      (matrixInterval m j row col).2 ≤ 2*m+1 := by
  fin_cases row <;> fin_cases col <;> simp only [matrixInterval] <;> omega

/-- Each periodic matrix entry is the cardinality of its derived residue interval. -/
theorem matrixEntry_eq_interval {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (row col : Fin 3) :
    matrixEntry m (affine hm hj hjm) row (columnShift col) =
      (matrixInterval m j row col).2 - (matrixInterval m j row col).1 := by
  rw [matrixEntry_original hm hj hjm]
  have hfilter :
      ((List.range (2*m+1)).filter fun a => inRow m row
        (((a+1 : ℕ) : ℤ) + (2*m+1 : ℕ)*familyShift m j (a+1) +
          (2*m+1 : ℕ)*columnShift col)) =
      ((List.range (2*m+1)).filter fun a => decide
        ((matrixInterval m j row col).1 ≤ a ∧
          a < (matrixInterval m j row col).2)) := by
    apply List.filter_congr
    intro a ha
    exact original_inRow_iff hm hj hjm row col a (List.mem_range.mp ha)
  rw [hfilter, range_filter_interval _ _ _ (matrixInterval_bounds hm hj hjm row col).1]
  have h := matrixInterval_bounds hm hj hjm row col
  rw [min_eq_right h.2, min_eq_right (h.1.trans h.2)]

/-- The actual affine-window block intersections give the manuscript's matrix
for every allowed pair `(m,j)`, not only the certificate examples. -/
theorem matrixWindow_eq_prescribedMatrix {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    matrixWindow m (affine hm hj hjm) = prescribedMatrix m j := by
  change List.ofFn (fun row : Fin 3 => List.ofFn (fun col : Fin 3 =>
    matrixEntry m (affine hm hj hjm) row (columnShift col))) = _
  simp_rw [matrixEntry_eq_interval hm hj hjm]
  norm_num [List.ofFn_succ, matrixInterval, prescribedMatrix]
  omega

/-- Functional form of the displayed matrix; its entries are natural multiplicities. -/
def prescribedArray (m j : ℕ) : Fin 3 → Fin 3 → ℕ :=
  ![![1,m-j,j-1], ![0,1,0], ![j-1,m-j,1]]

/-- Pointwise version, suitable for Schur dimension sums. -/
theorem matrixEntry_eq_prescribedArray {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (row col : Fin 3) :
    matrixEntry m (affine hm hj hjm) row (columnShift col) =
      prescribedArray m j row col := by
  rw [matrixEntry_eq_interval hm hj hjm]
  fin_cases row <;> fin_cases col <;>
    norm_num [matrixInterval, prescribedArray] <;> omega

end Guralnick.Family
