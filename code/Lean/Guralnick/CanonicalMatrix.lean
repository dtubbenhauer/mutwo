import Guralnick.FamilyLength
import Guralnick.CanonicalGallery

/-!
# Recovering the aggregate parameters from an actual matrix

The object is a nonnegative 3-by-3 matrix with row sums `(m,1,m)` and equal
outer column sums. Its parameters are extracted from its entries; the
parametrized form, feasibility, dimension polynomial and type-F identity
are proved, rather than assumed as properties of a numerical encoding.
-/

namespace Guralnick.CanonicalMatrix

open scoped BigOperators

structure PacketMatrix (m : ℕ) where
  entries : Fin 3 → Fin 3 → ℕ
  first_row : entries 0 0 + entries 0 1 + entries 0 2 = m
  middle_row : entries 1 0 + entries 1 1 + entries 1 2 = 1
  last_row : entries 2 0 + entries 2 1 + entries 2 2 = m
  outer_columns : entries 0 0 + entries 1 0 + entries 2 0 =
    entries 0 2 + entries 1 2 + entries 2 2

namespace PacketMatrix

variable {m : ℕ} (A : PacketMatrix m)

def rank : ℕ := A.entries 0 0 + A.entries 1 0 + A.entries 2 0
def corank : ℤ := (m : ℤ) - A.rank
def a : ℤ := A.entries 0 0
def s : ℤ := A.entries 1 2 + A.entries 2 2
def beta : ℤ := A.entries 1 0
def delta : ℤ := A.entries 1 0 + A.entries 1 1

theorem rank_le : A.rank ≤ m := by
  have h0 := A.first_row
  have h1 := A.middle_row
  have h2 := A.last_row
  have hc := A.outer_columns
  unfold rank
  omega

theorem corank_nonnegative : 0 ≤ A.corank := by
  have h := A.rank_le
  unfold corank
  omega

theorem a_nonnegative : 0 ≤ A.a := Int.natCast_nonneg _

theorem s_nonnegative : 0 ≤ A.s := add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

/-- The signed parametrization is derived entry by entry from row and
column sums. There is no parameter-existence assumption. -/
theorem reconstruct :
    (fun i j => (A.entries i j : ℤ)) =
      PeriodicMatrix.aggregateArray m A.rank A.a A.s A.beta A.delta := by
  have h0 := A.first_row
  have h1 := A.middle_row
  have h2 := A.last_row
  have hc := A.outer_columns
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [PeriodicMatrix.aggregateArray, a, s, beta, delta, rank] at * <;>
    (try simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] at *) <;> omega

theorem middle_cases : DegreeBounds.MiddleRow A.beta A.delta := by
  have h := A.middle_row
  unfold DegreeBounds.MiddleRow beta delta
  omega

theorem delta_zero_s_positive : A.delta = 0 → 1 ≤ A.s := by
  have h := A.middle_row
  unfold delta s
  omega

theorem line_feasible : A.a ≤ A.corank + A.s := by
  have h0 := A.first_row
  have hc := A.outer_columns
  unfold a corank s rank
  omega

theorem hyperplane_feasible : A.s + A.delta - 1 ≤ A.corank + A.a + A.beta := by
  have h1 := A.middle_row
  have h2 := A.last_row
  have hc := A.outer_columns
  unfold s delta corank a beta rank
  omega

theorem boundary_first (hl : A.corank = 0) : A.a ≤ A.s := by
  have h := A.line_feasible
  rw [hl, zero_add] at h
  exact h

theorem boundary_last (hl : A.corank = 0) : A.s ≤ A.a+1-A.delta+A.beta := by
  have h := A.hyperplane_feasible
  rw [hl] at h
  omega

/-- The actual finite periodic-dimension sum gives the manuscript's
codimension polynomial for every matrix in this class. -/
theorem dimension :
    PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)) =
      2 * A.rank * (2 * (m : ℤ) + 1 - A.rank) -
        CanonicalGallery.codimension A.corank A.a A.s A.beta A.delta := by
  rw [A.reconstruct]
  have hm := A.middle_cases
  have hb : A.beta = 0 ∨ A.beta = 1 := by rcases hm with h | h | h <;> aesop
  have hd : A.delta = 0 ∨ A.delta = 1 := by rcases hm with h | h | h <;> aesop
  rw [PeriodicMatrix.aggregate_dimension _ _ _ _ _ _ hb hd]
  rfl

theorem raw_gap :
    (2*(m : ℤ)^2+2*m-3) -
      PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)) =
      CanonicalGallery.gap A.corank A.a A.s A.beta A.delta := by
  rw [A.dimension]
  unfold CanonicalGallery.gap corank
  ring

theorem typeF_rank_positive (ha : A.a = 1) : 1 ≤ A.rank := by
  unfold a at ha
  unfold rank
  omega

/-- The type-F matrix is exactly the original prescribed family matrix,
with the member index recovered as its actual relative rank. -/
theorem typeF_identification (ha : A.a = 1) (hs : A.s = 1)
    (hb : A.beta = 0) (hd : A.delta = 1) :
    A.entries = Family.prescribedArray m A.rank := by
  have hr1 := A.typeF_rank_positive ha
  have hrm := A.rank_le
  have h := A.reconstruct
  rw [ha, hs, hb, hd] at h
  funext i j
  have hij := congrFun (congrFun h i) j
  fin_cases i <;> fin_cases j <;>
    norm_num [PeriodicMatrix.aggregateArray, Family.prescribedArray] at hij ⊢ <;> omega

end PacketMatrix

end Guralnick.CanonicalMatrix
