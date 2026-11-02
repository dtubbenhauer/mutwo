import Guralnick.OrbitMatrixInjectivity

/-! # Row and winding labels of the actual supported affine window -/
noncomputable section
namespace Guralnick.OrbitDimensionLabels
open Hecke CanonicalSchur OrbitMatrixElementary ElementaryCoxeterPackets
variable {N : ℕ} [NeZero N]

/-- The actual contiguous output packet containing a residue. -/
def row (A : FiniteBlocks.Composition N) (i : Fin N) : Fin A.packets.length :=
  packet A.packets (Fin.cast A.total.symm i)

theorem row_eq_iff (A : FiniteBlocks.Composition N) (i : Fin N)
    (r : Fin A.packets.length) : row A i=r ↔
    (A.packets.take r.val).sum ≤ i.val ∧ i.val<(A.packets.take (r.val+1)).sum := by
  rw [row,packet_eq_iff,List.sum_take_succ _ _ r.isLt]
  rfl

theorem row_mem (A : FiniteBlocks.Composition N) (i : Fin N) :
    i∈rowSet A (row A i) := by
  simp only [rowSet,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (row_eq_iff A i (row A i)).mp rfl

theorem row_monotone (A : FiniteBlocks.Composition N) : Monotone (row A) := by
  intro i j hij
  apply packet_monotone
  exact hij

/-- Convert the literal inverse winding -1,0,1 to its displayed column. -/
def col (w : AffinePermutation N) (hs : WindowPacketMatrix.Supported w) (i : Fin N) : Fin 3 :=
  ⟨((w⁻¹).winding i+1).toNat,by have h:=hs i; omega⟩

theorem col_val (w : AffinePermutation N) (hs : WindowPacketMatrix.Supported w) (i : Fin N) :
    ((col w hs i).val : ℤ)=(w⁻¹).winding i+1 := by
  have h:=hs i
  simp only [col]
  omega

theorem columnShift_val (c : Fin 3) : Family.columnShift c=(c.val : ℤ)-1 := by
  fin_cases c <;> norm_num [Family.columnShift]

theorem col_eq_iff (w : AffinePermutation N) (hs : WindowPacketMatrix.Supported w)
    (i : Fin N) (c : Fin 3) : col w hs i=c ↔ (w⁻¹).winding i=Family.columnShift c := by
  rw [Fin.ext_iff,columnShift_val]
  have h:=col_val w hs i
  omega

/-- The existing matrix entries are precisely the row/column histogram. -/
theorem compositionEntries_eq (A : FiniteBlocks.Composition N) (w : AffinePermutation N)
    (hs : WindowPacketMatrix.Supported w) (r : Fin A.packets.length) (c : Fin 3) :
    OrbitMatrix.compositionEntries A w r c =
      (Finset.univ.filter fun i : Fin N => row A i=r ∧ col w hs i=c).card := by
  unfold OrbitMatrix.compositionEntries
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,row_eq_iff,col_eq_iff]
  tauto

/-- Actual left descents supply the only within-row order used by the count. -/
theorem winding_antitone_on_rows (c : WindowCoxeter N) (A : FiniteBlocks.Composition N)
    (hA : A.cut.val=0) (w : AffinePermutation N)
    (hw : ∀ s∈A.index.val,c.system.IsLeftDescent w s)
    (i j : Fin N) (hij : i≤j) (hrow : row A i=row A j) :
    (w⁻¹).winding j≤(w⁻¹).winding i := by
  apply inverse_winding_antitone_row c A hA w hw (row A i)
  · exact row_mem A i
  · rw [hrow]
    exact row_mem A j
  · exact hij

#print axioms compositionEntries_eq
#print axioms winding_antitone_on_rows
end Guralnick.OrbitDimensionLabels
