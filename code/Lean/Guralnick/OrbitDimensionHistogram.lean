import Guralnick.FamilyLength

/-!
# A histogram expands the periodic dimension into pairs of actual objects

The matrix entry counts the objects with the specified row and winding
column. Expanding the two cardinalities in every product gives the literal
ordered-pair formula. This is finite counting, independent of Schubert
geometry or a dimension/length theorem.
-/
noncomputable section
namespace Guralnick.OrbitDimensionHistogram
open scoped BigOperators Classical
variable {N R : ℕ}

/-- The actual row/column histogram of a finite labeled set. -/
def histogram (row : Fin N → Fin R) (col : Fin N → Fin 3) (r : Fin R) (c : Fin 3) : ℕ :=
  (Finset.univ.filter (fun a => row a=r ∧ col a=c)).card

theorem histogram_eq_sum (row : Fin N → Fin R) (col : Fin N → Fin 3)
    (r : Fin R) (c : Fin 3) :
    (histogram row col r c : ℤ) =
      ∑ a : Fin N, if row a=r ∧ col a=c then (1 : ℤ) else 0 := by
  simp [histogram,Finset.sum_boole]

/-- Sum over the bins of a histogram equals sum over its actual objects. -/
theorem histogram_sum (row : Fin N → Fin R) (col : Fin N → Fin 3)
    (f : Fin R → Fin 3 → ℤ) :
    (∑ r,∑ c,(histogram row col r c : ℤ)*f r c) =
      ∑ a : Fin N,f (row a) (col a) := by
  calc
    _ = ∑ r : Fin R,∑ c : Fin 3,∑ a : Fin N,
        if row a=r ∧ col a=c then f r c else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro c _
      rw [histogram_eq_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = ∑ a : Fin N,∑ r : Fin R,∑ c : Fin 3,
        if row a=r ∧ col a=c then f r c else 0 := by
      calc
        _ = ∑ r : Fin R,∑ a : Fin N,∑ c : Fin 3,
            if row a=r ∧ col a=c then f r c else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      simp [ite_and]

/-- Exact ordered-pair expansion of the finite periodic dimension sum. -/
theorem dimension_histogram (row : Fin N → Fin R) (col : Fin N → Fin 3) :
    PeriodicMatrix.dimension (fun r c => (histogram row col r c : ℤ)) =
      ∑ a : Fin N,∑ b : Fin N,
        ((if (col a).val+1 < (col b).val then (1 : ℤ) else 0)+
          (if row b ≤ row a ∧ col a < col b then 1 else 0)) := by
  let F (r : Fin R) (c : Fin 3) (k : Fin R) (h : Fin 3) : ℤ :=
    (if c.val+1 < h.val then 1 else 0)+
      (if k.val ≤ r.val ∧ c.val < h.val then 1 else 0)
  calc
    _ = ∑ r : Fin R,∑ c : Fin 3,(histogram row col r c : ℤ)*
        (∑ k : Fin R,∑ h : Fin 3,(histogram row col k h : ℤ)*F r c k h) := by
      simp only [PeriodicMatrix.dimension,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro h _
      dsimp only [F]
      split_ifs <;> ring
    _ = ∑ a : Fin N,∑ k : Fin R,∑ h : Fin 3,
        (histogram row col k h : ℤ)*F (row a) (col a) k h := by
      exact histogram_sum row col _
    _ = ∑ a : Fin N,∑ b : Fin N,F (row a) (col a) (row b) (col b) := by
      apply Finset.sum_congr rfl
      intro a _
      exact histogram_sum row col _
    _ = _ := rfl

#print axioms histogram_sum
#print axioms dimension_histogram
end Guralnick.OrbitDimensionHistogram
