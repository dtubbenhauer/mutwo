import Guralnick.OrbitDimensionInversions

/-! # Expanding the periodic dimension into unordered residue pairs -/
noncomputable section
namespace Guralnick.OrbitDimensionPairs
open OrbitDimensionInversions
open scoped BigOperators

/-- Pairing the two orientations of each pair in a finite linear order. -/
theorem sum_pairs {n : ℕ} (F : Fin n → Fin n → ℤ) (hdiag : ∀ i,F i i=0) :
    (∑ i,∑ j,F i j) = ∑ i,∑ j,if i < j then F i j+F j i else 0 := by
  have hsplit (i j : Fin n) : F i j =
      (if i < j then F i j else 0)+(if j < i then F i j else 0) := by
    rcases lt_trichotomy i j with h|rfl|h
    · simp [h,not_lt_of_ge (le_of_lt h)]
    · simp [hdiag]
    · simp [h,not_lt_of_ge (le_of_lt h)]
  calc
    _ = (∑ i,∑ j,if i < j then F i j else 0)+
        (∑ i,∑ j,if j < i then F i j else 0) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact hsplit i j
    _ = (∑ i,∑ j,if i < j then F i j else 0)+
        (∑ i,∑ j,if i < j then F j i else 0) := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring

/-- Within equal rows, decreasing labels make the second matrix summand
exactly the decreasing-label contribution of the later residue. -/
theorem matrix_pair_sum {n r : ℕ} (row : Fin n → Fin r) (t : Fin n → ℤ)
    (hrow : Monotone row)
    (ht : ∀ i j,i ≤ j → row i=row j → t j ≤ t i) :
    (∑ i,∑ j,
      ((if t i+1 < t j then (1 : ℤ) else 0)+
        (if row j ≤ row i ∧ t i < t j then 1 else 0))) =
      ∑ i,∑ j,if i < j then pairExtra (t i) (t j) else 0 := by
  rw [sum_pairs _ (by intro i; simp)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij,if_pos hij]
    have hr := hrow (le_of_lt hij)
    have hn : ¬(row j ≤ row i ∧ t i < t j) := by
      intro h
      have he : row i=row j := le_antisymm hr h.1
      exact (not_lt_of_ge (ht i j (le_of_lt hij) he)) h.2
    simp only [if_neg hn,hr,true_and,add_zero,pairExtra]
    ring
  · simp only [if_neg hij]

#print axioms matrix_pair_sum
end Guralnick.OrbitDimensionPairs
