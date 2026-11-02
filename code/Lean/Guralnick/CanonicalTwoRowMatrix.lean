import Guralnick.CanonicalAuxiliary
import Guralnick.FamilyLength

/-! # The actual two-row matrix parameters of a one-line web -/
namespace Guralnick.CanonicalTwoRowMatrix
open scoped BigOperators

structure MatrixData (N f : ℕ) where
  entry : Fin 2 → Fin 3 → ℕ
  first_row : entry 0 0+entry 0 1+entry 0 2=f
  last_row : entry 1 0+entry 1 1+entry 1 2=N-f
  balance : entry 0 0+entry 1 0=entry 0 2+entry 1 2

namespace MatrixData
variable {N f : ℕ} (A : MatrixData N f)

def rank : ℕ := A.entry 0 0+A.entry 1 0
def n : ℤ := (N : ℤ)-2*A.rank
def d : ℤ := (f : ℤ)-A.rank
def a : ℤ := A.entry 0 0
def b : ℤ := A.entry 1 2

def array (N f r a b : ℤ) : Fin 2 → Fin 3 → ℤ :=
  ![![a,f-r+b-a,r-b],![r-a,N-f-r+a-b,b]]

theorem reconstruct (hf : f≤N) : (fun i j => (A.entry i j : ℤ)) =
    array N f A.rank A.a A.b := by
  funext i j
  have h0 := A.first_row
  have h1 := A.last_row
  have he := A.balance
  fin_cases i <;> fin_cases j <;>
    norm_num [array,a,b,rank] at * <;> try omega
  · change (A.entry 0 2 : ℤ) = (A.entry 0 0 : ℤ)+A.entry 1 0-A.entry 1 2
    omega
  · rfl

theorem a_nonnegative : 0≤A.a := Int.natCast_nonneg _
theorem b_nonnegative : 0≤A.b := Int.natCast_nonneg _

theorem line_feasible : A.a≤A.d+A.b := by
  have h := A.first_row
  have he := A.balance
  unfold a d b rank
  omega

theorem quotient_feasible (hf : f≤N) : A.b≤A.n-A.d+A.a := by
  have h := A.last_row
  unfold a b n d rank
  omega

theorem rank_bound (hf : f≤N) : 2*A.rank≤N := by
  have h0 := A.first_row
  have h1 := A.last_row
  have he := A.balance
  unfold rank
  omega

end MatrixData

theorem dimension_two (A : Fin 2 → Fin 3 → ℤ) :
    PeriodicMatrix.dimension A =
      (A 0 0+A 1 0)*(A 0 2+A 1 2)+
      A 0 0*(A 0 1+A 0 2)+A 0 1*A 0 2+
      A 1 0*(A 0 1+A 0 2+A 1 1+A 1 2)+A 1 1*(A 0 2+A 1 2) := by
  simp only [PeriodicMatrix.dimension,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ]
  norm_num
  ring

theorem array_dimension (N f r a b : ℤ) :
    PeriodicMatrix.dimension (MatrixData.array N f r a b) =
      2*r*(N-r)-CanonicalOneLine.codimension (N-2*r) (f-r) a b := by
  rw [dimension_two]
  simp only [MatrixData.array,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  unfold CanonicalOneLine.codimension
  ring

namespace MatrixData
variable {N f : ℕ} (A : MatrixData N f)

theorem dimension (hf : f≤N) :
    PeriodicMatrix.dimension (fun i j => (A.entry i j : ℤ)) =
      2*A.rank*((N : ℤ)-A.rank)-CanonicalOneLine.codimension A.n A.d A.a A.b := by
  rw [A.reconstruct hf,array_dimension]
  rfl

/-- Subtracting the actual orbit dimension from the one-line word cost
produces exactly the degree-gap expression used in the Gaussian test. -/
theorem normalization_gap (hf : f≤N) (j : ℤ) :
    (2*j*(N-j)-((N : ℤ)-f-j+1)) -
      PeriodicMatrix.dimension (fun i k => (A.entry i k : ℤ)) =
      CanonicalOneLine.lengthGap A.n (j-A.rank) A.d A.a A.b := by
  rw [A.dimension hf]
  unfold CanonicalOneLine.lengthGap n d
  ring

theorem entries_eq_of_parameters (hf : f≤N) {B : MatrixData N f}
    (hr : A.rank=B.rank) (ha : A.a=B.a) (hb : A.b=B.b) : A.entry=B.entry := by
  have he := A.reconstruct hf
  rw [hr,ha,hb,← B.reconstruct hf] at he
  funext i j
  have hij := congrFun (congrFun he i) j
  exact_mod_cast hij

/-- Distinct leading cases are separated by f=j versus f>j. -/
theorem leading_b {j : ℕ} (hr : A.rank=j)
    (h : (1≤A.d ∧ A.b=0) ∨ (A.d=0 ∧ A.b=1)) :
    A.b = if f=j then 1 else 0 := by
  unfold d at h
  rw [hr] at h
  split_ifs <;> rcases h with ⟨hd,hb⟩ | ⟨hd,hb⟩ <;> omega

end MatrixData
end Guralnick.CanonicalTwoRowMatrix
