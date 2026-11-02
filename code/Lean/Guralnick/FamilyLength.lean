import Guralnick.FamilyMatrix
import Guralnick.Normalization

/-!
# Periodic matrix dimension sums

For matrices supported in the three columns one period apart, the defining
periodic dimension sum reduces to the current and preceding row periods.
The formulas below evaluate that sum, independently of the proposed length
polynomials. Its interpretation as Coxeter length is a separate general
Schur dictionary theorem from the literature.
-/

namespace Guralnick.PeriodicMatrix

open scoped BigOperators

/-- All admissible row periods in the dimension sum for three-column support.
The row period is zero-based and the column coordinates have been divided by
the common row period. -/
theorem admissible_periods {n : ℕ} (hn : 0 < n) (i k : Fin n)
    (c h : Fin 3) (t : ℤ) :
    ((k.val : ℤ) + n*t ≤ i.val ∧ (c.val : ℤ) < h.val + t) ↔
      (t = -1 ∧ c.val+1 < h.val) ∨
      (t = 0 ∧ k.val ≤ i.val ∧ c.val < h.val) := by
  have hi := i.isLt
  have hk := k.isLt
  have hc := c.isLt
  have hh := h.isLt
  constructor
  · intro hab
    have htlow : -1 ≤ t := by omega
    have htup : t ≤ 0 := by
      by_contra hpos
      have ht : 1 ≤ t := by omega
      have hmul : (n : ℤ) ≤ n*t := by
        exact le_mul_of_one_le_right (by omega) ht
      omega
    have ht : t = -1 ∨ t = 0 := by omega
    rcases ht with rfl | rfl <;> norm_num at * <;> omega
  · rintro (⟨rfl, hch⟩ | ⟨rfl,hki,hch⟩) <;> norm_num <;> omega

/-- The finite form of the periodic dimension sum. A preceding-period pair
contributes when `c+1<h`; a current-period pair when `k≤i` and `c<h`.
No family-specific formula occurs in this definition. -/
def dimension {n : ℕ} (A : Fin n → Fin 3 → ℤ) : ℤ :=
  ∑ i, ∑ c, ∑ k, ∑ h,
    ((if c.val+1 < h.val then A i c * A k h else 0) +
      (if k.val ≤ i.val ∧ c.val < h.val then A i c * A k h else 0))

/-- Exact dimension polynomial of the desired three-row matrix. -/
theorem family_dimension {m j : ℕ} (_hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) :
    dimension (fun r c => (Family.prescribedArray m j r c : ℤ)) =
      gapFormula m j := by
  simp only [dimension, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Family.prescribedArray, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Nat.cast_zero, Nat.cast_one]
  norm_num
  rw [Int.ofNat_sub hjm, Int.ofNat_sub hj]
  unfold gapFormula
  push_cast
  ring

/-- The dimension calculation applies to the actual block intersections. -/
theorem actual_family_dimension {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) :
    dimension (fun row col =>
      (matrixEntry m (Family.affine hm hj hjm) row (Family.columnShift col) : ℤ)) =
      gapFormula m j := by
  simp_rw [Family.matrixEntry_eq_prescribedArray hm hj hjm]
  exact family_dimension hm hj hjm

/-- The signed parametrization of a general supported aggregate matrix.
Nonnegativity and its derivation from margins are separate statements. -/
def aggregateArray (m r a s beta delta : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![a,m-r+s-a,r-s], ![beta,delta-beta,1-delta],
    ![r-a-beta,m-r+1-s-delta+a+beta,s+delta-1]]

/-- Expansion of the generic periodic sum with the matrix left opaque. -/
theorem dimension_three (A : Fin 3 → Fin 3 → ℤ) :
    dimension A =
      (A 0 0+A 1 0+A 2 0)*(A 0 2+A 1 2+A 2 2) +
      A 0 0*(A 0 1+A 0 2)+A 0 1*A 0 2 +
      A 1 0*(A 0 1+A 0 2+A 1 1+A 1 2)+A 1 1*(A 0 2+A 1 2) +
      A 2 0*(A 0 1+A 0 2+A 1 1+A 1 2+A 2 1+A 2 2)+
      A 2 1*(A 0 2+A 1 2+A 2 2) := by
  simp only [dimension, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

/-- The periodic dimension sum evaluated on the general parametrization.
The binary middle-row hypothesis is used explicitly. -/
theorem aggregate_dimension (m r a s beta delta : ℤ)
    (hbeta : beta = 0 ∨ beta = 1) (hdelta : delta = 0 ∨ delta = 1) :
    dimension (aggregateArray m r a s beta delta) =
      2*r*(2*m+1-r) -
        (s*(m-r+s) + a*(m-r+a-s+1) + beta*(m-r+a+beta) +
          (delta-beta)*(s+delta-1)) := by
  rw [dimension_three]
  rcases hbeta with rfl | rfl <;> rcases hdelta with rfl | rfl <;>
    simp only [aggregateArray, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring

end Guralnick.PeriodicMatrix
