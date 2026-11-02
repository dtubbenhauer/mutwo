import Guralnick.AffineReflection
import Guralnick.WindowPacketMatrix
import Guralnick.CanonicalMultiplicityBounds

/-!
# The two reflected one-line families

Reflection reverses rows and columns of the actual inverse-winding count
matrix. The raw multiplicity bound is calculated at each original index;
only the ordinary canonical coefficient is transported by diagram symmetry.
-/

noncomputable section
namespace Guralnick.PacketReflection
open scoped BigOperators
open AffineReflection WindowPacketMatrix CanonicalMatrix

theorem source_node (m : ℕ) (i : Fin (2*m+1)) :
    node i ∈ (ParabolicWeb.Family.source m).val ↔
      i ∈ (ParabolicWeb.Family.source m).val := by
  have hi:=i.isLt
  simp only [ParabolicWeb.Family.source, ParabolicWeb.Family.sourceSet,
    Finset.mem_filter, Finset.mem_univ, true_and, node]
  split_ifs <;> omega

theorem output_node (m : ℕ) (i : Fin (2*m+1)) :
    node i ∈ (ParabolicWeb.Family.output m).val ↔
      i ∈ (ParabolicWeb.Family.output m).val := by
  have hi:=i.isLt
  simp only [ParabolicWeb.Family.output, ParabolicWeb.Family.outputSet,
    ParabolicWeb.Family.sourceSet, ParabolicWeb.Family.cyclicSet,
    Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, node]
  split_ifs <;> omega

theorem doubleMaximal_reflect {m : ℕ} (hm : 2≤m)
    (c : Hecke.WindowCoxeter (2*m+1)) (w : AffinePermutation (2*m+1))
    (hw : CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output m)
      (ParabolicWeb.Family.source m) w) :
    CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output m)
      (ParabolicWeb.Family.source m) (reflect w) := by
  letI : NeZero (2*m+1):=⟨by omega⟩
  constructor
  · intro i hi
    have h:=hw.1 (node i) ((output_node m i).mpr hi)
    simpa only [node_node] using (left_descent_reflect (by omega) c w (node i)).mpr h
  · intro i hi
    have h:=hw.2 (node i) ((source_node m i).mpr hi)
    simpa only [node_node] using (right_descent_reflect (by omega) c w (node i)).mpr h

@[simp] theorem rowOf_rev (m : ℕ) (i : Fin (2*m+1)) :
    rowOf m i.rev=(rowOf m i).rev := by
  have hi:=i.isLt
  apply Fin.ext
  unfold rowOf
  simp only [Fin.val_rev, Nat.add_sub_add_right]
  split_ifs <;> norm_num <;> omega

@[simp] theorem columnShift_rev (c : Fin 3) :
    Family.columnShift c.rev = -Family.columnShift c := by
  fin_cases c <;> norm_num [Family.columnShift]

theorem supported_reflect {n : ℕ} {w : AffinePermutation n} (h : Supported w) :
    Supported (reflect w) := by
  intro i
  rw [←reflect_inv, reflect_winding]
  have hi:=h i.rev
  omega

/-- Literal count matrices transform by reversing both finite index orders. -/
theorem entries_reflect (m : ℕ) (w : AffinePermutation (2*m+1)) (row col : Fin 3) :
    entries m (reflect w) row col=entries m w row.rev col.rev := by
  classical
  simp only [entries, card_filter_sum]
  have he:=Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (2*m+1)))
    (fun i => if rowOf m i=row ∧ ((reflect w)⁻¹).winding i=Family.columnShift col
      then (1 : ℕ) else 0)
  rw [←he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.revPerm_apply, rowOf_rev, Fin.rev_eq_iff, ←reflect_inv,
    reflect_winding, Fin.rev_rev, columnShift_rev]
  have hh : -(w⁻¹).winding i=Family.columnShift col ↔
      (w⁻¹).winding i= -Family.columnShift col := by omega
  simp only [hh]

theorem rank_reflect (m : ℕ) (w : AffinePermutation (2*m+1)) (hw : Supported w) :
    (packetMatrix m (reflect w) (supported_reflect hw)).rank=(packetMatrix m w hw).rank := by
  have h:=(packetMatrix m w hw).outer_columns
  simp only [PacketMatrix.rank, packetMatrix, entries_reflect]
  norm_num only [Fin.reduceRev]
  change entries m w 2 2+entries m w 1 2+entries m w 0 2 =
    entries m w 0 0+entries m w 1 0+entries m w 2 0
  change entries m w 0 0+entries m w 1 0+entries m w 2 0 =
    entries m w 0 2+entries m w 1 2+entries m w 2 2 at h
  omega

theorem parameters_reflect (m : ℕ) (w : AffinePermutation (2*m+1)) (hw : Supported w) :
    let A:=packetMatrix m w hw
    let B:=packetMatrix m (reflect w) (supported_reflect hw)
    B.corank=A.corank ∧ B.a=A.s+A.delta-1 ∧
      B.s=A.a+A.beta ∧ B.beta=1-A.delta ∧ B.delta=1-A.beta := by
  dsimp only
  have hr:=rank_reflect m w hw
  dsimp only [packetMatrix] at hr
  have hm:=(packetMatrix m w hw).middle_row
  have h2:=(packetMatrix m w hw).reconstruct
  have ha:=congrFun (congrFun h2 2) 2
  simp only [PacketMatrix.corank, rank_reflect, PacketMatrix.a, PacketMatrix.s,
    PacketMatrix.beta, PacketMatrix.delta, packetMatrix, entries_reflect]
  simp only [show (0 : Fin 3).rev=2 from rfl, show (1 : Fin 3).rev=1 from rfl,
    show (2 : Fin 3).rev=0 from rfl]
  simp only [PeriodicMatrix.aggregateArray, Matrix.cons_val_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons] at ha
  dsimp [PacketMatrix.a, PacketMatrix.s, PacketMatrix.beta, PacketMatrix.delta,
    PacketMatrix.rank, packetMatrix] at ha hm
  omega

/-- The ordinary canonical coefficients at all indices used by the
critical readout are fixed under reflection of the upper index. -/
theorem canonical_fixed_source {m : ℕ} (hm : 2≤m)
    {c : Hecke.WindowCoxeter (2*m+1)} (K : Hecke.KLRealization c)
    (H : DiagramInvarianceInput K) (w : AffinePermutation (2*m+1)) :
    K.standard.repr (K.canonical (reflect w)) (AffinePermutation.longest (2*m+1)) =
      K.standard.repr (K.canonical w) (AffinePermutation.longest (2*m+1)) := by
  letI : NeZero (2*m+1):=⟨by omega⟩
  simpa only [reflect_longest] using canonical_reflection (by omega) K H
    (AffinePermutation.longest (2*m+1)) w

theorem canonical_at_family {m j : ℕ} (hm : 2≤m) (hj : 1≤j) (hjm : j≤m)
    {c : Hecke.WindowCoxeter (2*m+1)} (K : Hecke.KLRealization c)
    (H : DiagramInvarianceInput K) (w : AffinePermutation (2*m+1)) :
    K.standard.repr (K.canonical (reflect w)) (Family.upper hm hj hjm) =
      K.standard.repr (K.canonical w) (Family.upper hm hj hjm) := by
  letI : NeZero (2*m+1):=⟨by omega⟩
  simpa only [reflect_upper] using canonical_reflection (by omega) K H
    (Family.upper hm hj hjm) w

theorem canonical_at_spherical {m : ℕ} (hm : 2≤m)
    {c : Hecke.WindowCoxeter (2*m+1)} (K : Hecke.KLRealization c)
    (H : DiagramInvarianceInput K) (w : AffinePermutation (2*m+1)) (r : ℕ) :
    K.standard.repr (K.canonical (reflect w)) (CanonicalSpherical.index m r) =
      K.standard.repr (K.canonical w) (CanonicalSpherical.index m r) := by
  letI : NeZero (2*m+1):=⟨by omega⟩
  simpa only [reflect_spherical] using canonical_reflection (by omega) K H
    (CanonicalSpherical.index m r) w

end Guralnick.PacketReflection
