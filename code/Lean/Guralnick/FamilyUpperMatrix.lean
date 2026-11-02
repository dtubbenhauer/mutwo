import Guralnick.FamilyMatrix
import Guralnick.AffineGroup

/-! # The same spherical source matrix for u and u w₀ -/
namespace Guralnick

/-- Right multiplication by the finite longest element only permutes the
full source packet, including each affine translate. -/
theorem matrixEntry_mul_longest (m : ℕ) (w : AffinePermutation (2*m+1))
    (row : Fin 3) (shift : ℤ) :
    matrixEntry m (w * AffinePermutation.longest (2*m+1)) row shift =
      matrixEntry m w row shift := by
  unfold matrixEntry AffinePermutation.window
  have h := Fin.revPerm.ofFn_comp_perm w.entry
  have he : (w * AffinePermutation.longest (2*m+1)).entry = w.entry ∘ Fin.revPerm := by
    funext i
    exact AffinePermutation.mul_longest_entry w i
  rw [he]
  exact (h.filter _).length_eq

/-- No row block contains an integer outside the principal period. -/
theorem inRow_false_of_outside (m : ℕ) (row : Fin 3) (x : ℤ)
    (h : x ≤ 0 ∨ (2*m+1 : ℕ) < x) : inRow m row x = false := by
  fin_cases row <;> simp [inRow] <;> omega

namespace Family

theorem upper_matrixEntry_eq_prescribedArray {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) (row col : Fin 3) :
    matrixEntry m (upper hm hj hjm) row (columnShift col) =
      prescribedArray m j row col := by
  rw [upper, matrixEntry_mul_longest]
  exact matrixEntry_eq_prescribedArray hm hj hjm row col

theorem upper_matrixWindow_eq_prescribedMatrix {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    matrixWindow m (upper hm hj hjm) = prescribedMatrix m j := by
  have he : matrixEntry m (upper hm hj hjm) = matrixEntry m (affine hm hj hjm) := by
    funext row shift
    exact matrixEntry_mul_longest m _ row shift
  unfold matrixWindow
  rw [he]
  exact matrixWindow_eq_prescribedMatrix hm hj hjm

/-- All other source translates have zero block intersections. This
completes the full periodic matrix identification beyond the nine entries. -/
theorem matrixEntry_outside {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (row : Fin 3) (shift : ℤ) (hs : shift < -1 ∨ 1 < shift) :
    matrixEntry m (affine hm hj hjm) row shift = 0 := by
  rw [matrixEntry_original hm hj hjm]
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  have ha' := List.mem_range.mp ha
  have hδ : -1 ≤ familyShift m j (a+1) ∧ familyShift m j (a+1) ≤ 1 := by
    unfold familyShift
    split_ifs <;> norm_num
  have hN : (0 : ℤ) ≤ (2*m+1 : ℕ) := by omega
  have hl := mul_le_mul_of_nonneg_left hδ.1 hN
  have hu := mul_le_mul_of_nonneg_left hδ.2 hN
  have hout : ((a+1 : ℕ) : ℤ) + (2*m+1 : ℕ)*familyShift m j (a+1) +
        (2*m+1 : ℕ)*shift ≤ 0 ∨
      (2*m+1 : ℕ) < ((a+1 : ℕ) : ℤ) +
        (2*m+1 : ℕ)*familyShift m j (a+1) + (2*m+1 : ℕ)*shift := by
    rcases hs with hs | hs
    · have hh : shift ≤ -2 := by omega
      have hh' := mul_le_mul_of_nonneg_left hh hN
      left
      push_cast at *
      nlinarith
    · have hh : 2 ≤ shift := by omega
      have hh' := mul_le_mul_of_nonneg_left hh hN
      right
      push_cast at *
      nlinarith
  rw [inRow_false_of_outside m row _ hout]
  decide

theorem upper_matrixEntry_outside {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (row : Fin 3) (shift : ℤ) (hs : shift < -1 ∨ 1 < shift) :
    matrixEntry m (upper hm hj hjm) row shift = 0 := by
  rw [upper,matrixEntry_mul_longest]
  exact matrixEntry_outside hm hj hjm row shift hs

end Family
end Guralnick
