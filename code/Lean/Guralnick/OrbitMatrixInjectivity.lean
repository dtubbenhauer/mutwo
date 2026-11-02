import Guralnick.OrbitMatrixParabolic
import Guralnick.FiniteOrderedHistogram

/-! # Matrix labels determine maximal representatives, by sorted monomials -/
noncomputable section
namespace Guralnick.OrbitMatrixElementary
open Hecke ParabolicWeb CanonicalSchur ElementaryCoxeterPackets
variable {N : ℕ} [NeZero N]

theorem row_adjacent_index (A : FiniteBlocks.Composition N) (hA : A.cut.val=0)
    (r : Fin A.packets.length) (i j : Fin N) (hij : i.val+1=j.val)
    (hi : i∈rowSet A r) (hj : j∈rowSet A r) : j∈A.index.val := by
  have hiS : i.val<A.packets.sum := by simpa [A.total] using i.isLt
  have hjS : j.val<A.packets.sum := by simpa [A.total] using j.isLt
  have hpi := (packet_eq_iff A.packets ⟨i.val,hiS⟩ r).mpr ((mem_rowSet A r i).mp hi)
  have hpj := (packet_eq_iff A.packets ⟨j.val,hjS⟩ r).mpr ((mem_rowSet A r j).mp hj)
  have hs : packet A.packets ⟨i.val,hiS⟩ =
      packet A.packets ⟨i.val+1,by omega⟩ := by simpa only [hij] using hpi.trans hpj.symm
  have hn := (adjacent_same_iff A.packets A.positive i.val (by omega)).mp hs
  change j∈A.cutsᶜ
  rw [Finset.mem_compl,mem_cuts_zero A hA]
  simpa only [hij] using hn

/-- Left descents make the inverse winding weakly decreasing inside each row. -/
theorem inverse_winding_antitone_row (c : WindowCoxeter N)
    (A : FiniteBlocks.Composition N) (hA : A.cut.val=0) (w : AffinePermutation N)
    (hw : ∀ s∈A.index.val,c.system.IsLeftDescent w s) (r : Fin A.packets.length) :
    AntitoneOn (w⁻¹).winding (rowSet A r) := by
  intro i hi j hj hij
  have hbi := (mem_rowSet A r i).mp hi
  have hbj := (mem_rowSet A r j).mp hj
  have hchain : ∀ t, i.val≤t → ∀ ht : t<N, t≤j.val →
      (w⁻¹).winding ⟨t,ht⟩ ≤ (w⁻¹).winding i := by
    intro t hit
    induction t,hit using Nat.le_induction with
    | base => intro ht htj; exact le_rfl
    | succ t hit ih =>
      intro ht htj
      have ht₀ : t<N := by omega
      have ha : (⟨t,ht₀⟩ : Fin N)∈rowSet A r :=
        (mem_rowSet A r _).mpr (by dsimp; omega)
      have hb : (⟨t+1,ht⟩ : Fin N)∈rowSet A r :=
        (mem_rowSet A r _).mpr (by dsimp; omega)
      have hidx := row_adjacent_index A hA r ⟨t,ht₀⟩ ⟨t+1,ht⟩ rfl ha hb
      have hd := c.system.isRightDescent_inv_iff.mpr (hw _ hidx)
      have he := (c.finite_descent (w⁻¹) ⟨t,ht₀⟩ ⟨t+1,ht⟩ rfl).mp hd
      exact (winding_le_of_entry_lt (w⁻¹) ⟨t,ht₀⟩ ⟨t+1,ht⟩ he).trans
        (ih ht₀ (by omega))
  exact hchain j.val hij j.isLt le_rfl

theorem row_histogram_column (A : FiniteBlocks.Composition N) (w : AffinePermutation N)
    (r : Fin A.packets.length) (col : Fin 3) :
    ((rowSet A r).filter fun i => (w⁻¹).winding i=Family.columnShift col).card =
      OrbitMatrix.compositionEntries A w r col := by
  congr 1
  ext i
  simp only [rowSet,OrbitMatrix.compositionEntries,Finset.mem_filter,Finset.mem_univ,true_and]
  tauto

theorem inverse_winding_eq_of_matrix (c : WindowCoxeter N)
    (A : FiniteBlocks.Composition N) (hA : A.cut.val=0) (u v : AffinePermutation N)
    (su : WindowPacketMatrix.Supported u) (sv : WindowPacketMatrix.Supported v)
    (hu : ∀ s∈A.index.val,c.system.IsLeftDescent u s)
    (hv : ∀ s∈A.index.val,c.system.IsLeftDescent v s)
    (hmat : OrbitMatrix.compositionEntries A u = OrbitMatrix.compositionEntries A v) :
    (u⁻¹).winding = (v⁻¹).winding := by
  classical
  funext i
  let r := packet A.packets (Fin.cast A.total.symm i)
  have hi : i∈rowSet A r := (mem_rowSet A r i).mpr (packet_spec A.packets _)
  apply antitoneOn_eq_of_histogram (rowSet A r) (u⁻¹).winding (v⁻¹).winding
    (inverse_winding_antitone_row c A hA u hu r)
    (inverse_winding_antitone_row c A hA v hv r) _ i hi
  intro t
  by_cases ht : t = -1 ∨ t=0 ∨ t=1
  · rcases ht with ht|ht|ht <;> subst t
    · simpa only [←row_histogram_column,Family.columnShift,Matrix.cons_val_zero] using
        congrFun (congrFun hmat r) (0 : Fin 3)
    · simpa [←row_histogram_column,Family.columnShift] using
        congrFun (congrFun hmat r) (1 : Fin 3)
    · simpa [←row_histogram_column,Family.columnShift] using
        congrFun (congrFun hmat r) (2 : Fin 3)
  · have hzero (w : AffinePermutation N) (hw : WindowPacketMatrix.Supported w) :
        (rowSet A r).filter (fun i => (w⁻¹).winding i=t) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj he
      have hb := hw j
      omega
    rw [hzero u su,hzero v sv]

/-- The uniform matrix-injectivity clause is an elementary sorted-window theorem. -/
theorem matrix_injective (c : WindowCoxeter N)
    (A : FiniteBlocks.Composition N) (hA : A.cut.val=0) (u v : AffinePermutation N)
    (su : WindowPacketMatrix.Supported u) (sv : WindowPacketMatrix.Supported v)
    (hu : DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) u)
    (hv : DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) v)
    (hmat : OrbitMatrix.compositionEntries A u = OrbitMatrix.compositionEntries A v) : u=v :=
  eq_of_right_maximal_inverse_winding c hu.2 hv.2
    (inverse_winding_eq_of_matrix c A hA u v su sv hu.1 hv.1 hmat)

#print axioms matrix_injective
end Guralnick.OrbitMatrixElementary
