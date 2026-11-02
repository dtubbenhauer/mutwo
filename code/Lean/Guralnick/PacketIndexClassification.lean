import Guralnick.FamilyDescents
import Guralnick.PacketCumulative
import Guralnick.FamilyUpperMatrix
import Guralnick.OrbitLengthInput

/-!
# Recovering actual affine indices from packet types

These arguments use the generic injectivity of the periodic matrix label on
maximal double-coset representatives. The original family's matrix and its
maximality are proved independently; hence type F determines the actual
upper endpoint, rather than merely an abstract label with the same name.
-/
noncomputable section
namespace Guralnick.PacketIndexClassification
open WindowPacketMatrix CanonicalMatrix

/-- A type-F packet is the actual member of the prescribed family. -/
theorem typeF_index {m : ℕ} (hm : 2 ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) (O : OrbitMatrix.ThreeColumnLengthInput c)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output m)
      (ParabolicWeb.Family.source m) w)
    (ha : (packetMatrix m w hw).a = 1) (hs : (packetMatrix m w hw).s = 1)
    (hb : (packetMatrix m w hw).beta = 0) (hd : (packetMatrix m w hw).delta = 1) :
    w = Family.upper hm ((packetMatrix m w hw).typeF_rank_positive ha)
      (packetMatrix m w hw).rank_le := by
  let A := packetMatrix m w hw
  apply O.matrix_injective (FiniteBlocks.Family.output hm) rfl w _ hw
    (Family.upper_supported hm (A.typeF_rank_positive ha) A.rank_le)
  · simpa only [FiniteBlocks.Family.output_index,
      ← FiniteBlocks.Family.source_eq_standard] using hmax
  · simpa only [FiniteBlocks.Family.output_index,
      ← FiniteBlocks.Family.source_eq_standard] using
      Family.upper_doubleMaximal hm (A.typeF_rank_positive ha) A.rank_le c
  · funext row col
    rw [OrbitMatrix.compositionEntries_output,OrbitMatrix.compositionEntries_output]
    calc
      entries m w row col = Family.prescribedArray m A.rank row col :=
        congrFun (congrFun (A.typeF_identification ha hs hb hd) row) col
      _ = entries m (Family.upper hm (A.typeF_rank_positive ha) A.rank_le) row col := by
        rw [entries_eq_matrixEntry,Family.upper_matrixEntry_eq_prescribedArray]

/-- The full-spherical indices also have the bounded inverse-winding
support required by the general matrix dictionary. -/
theorem spherical_supported (m r : ℕ) : Supported (CanonicalSpherical.index m r) := by
  intro i
  rw [CanonicalSpherical.index_inverse]
  simp only [CanonicalSpherical.index,AffinePermutation.mul_winding,
    AffinePermutation.longest_winding,Pi.zero_apply,zero_add,
    AffinePermutation.longest_residue,Fin.revPerm_apply]
  change -1 ≤ Family.winding m (min r m) i.rev ∧
    Family.winding m (min r m) i.rev ≤ 1
  unfold Family.winding
  split_ifs <;> norm_num

/-- The actual inverse-residue packet entries of the spherical index. -/
theorem spherical_entries {m r : ℕ} (hr : r ≤ m) (row col : Fin 3) :
    entries m (CanonicalSpherical.index m r) row col =
      CanonicalSpherical.array m r row col := by
  rw [entries_eq_matrixEntry,CanonicalSpherical.index,matrixEntry_mul_longest,
    CanonicalSpherical.matrixEntry_eq_array hr]

/-- The three column totals are forced by the row margins and balance. -/
theorem packet_column_totals {m : ℕ} (A : PacketMatrix m) (col : Fin 3) :
    A.entries 0 col + A.entries 1 col + A.entries 2 col =
      if col.val = 1 then 2*m+1-2*A.rank else A.rank := by
  have h0 := A.first_row
  have h1 := A.middle_row
  have h2 := A.last_row
  have hc := A.outer_columns
  have hr := A.rank_le
  fin_cases col <;> simp only [Fin.val_zero,Fin.val_one,Fin.reduceFinMk,
    zero_ne_one,if_false,if_true,Nat.reduceEqDiff] <;>
    unfold PacketMatrix.rank at * <;> omega

/-- Every three-column full-spherical maximal index is the actual unmarked
rank-r index. This classification does not assume a special three-row form. -/
theorem spherical_index {m : ℕ} (hm : 2 ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) (O : OrbitMatrix.ThreeColumnLengthInput c)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.source m)
      (ParabolicWeb.Family.source m) w) :
    w = CanonicalSpherical.index m (packetMatrix m w hw).rank := by
  let A := packetMatrix m w hw
  apply O.matrix_injective (FiniteBlocks.Family.source hm) rfl w _ hw
    (spherical_supported m A.rank)
  · simpa only [FiniteBlocks.Family.source_index,
      ← FiniteBlocks.Family.source_eq_standard] using hmax
  · simpa only [FiniteBlocks.Family.source_index,
      ← FiniteBlocks.Family.source_eq_standard] using
      CanonicalSpherical.index_doubleMaximal A.rank_le c
  · funext row col
    rw [OrbitMatrix.compositionEntries_source,OrbitMatrix.compositionEntries_source,
      ← column_sum,← column_sum]
    change A.entries 0 col + A.entries 1 col + A.entries 2 col = _
    rw [packet_column_totals,spherical_entries A.rank_le,
      spherical_entries A.rank_le,spherical_entries A.rank_le]
    have hr := A.rank_le
    fin_cases col <;> norm_num [CanonicalSpherical.array,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] <;> omega

/-- The full packet type reconstructs the actual three-row matrix of Zᵣ. -/
theorem full_identification {m : ℕ} (A : PacketMatrix m)
    (ha : A.a = 0) (hs : A.s = 0) (hb : A.beta = 0) (hd : A.delta = 1) :
    A.entries = CanonicalSpherical.array m A.rank := by
  have hrm := A.rank_le
  have h := A.reconstruct
  rw [ha,hs,hb,hd] at h
  funext i j
  have hij := congrFun (congrFun h i) j
  fin_cases i <;> fin_cases j <;>
    norm_num [PeriodicMatrix.aggregateArray,CanonicalSpherical.array,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at hij ⊢ <;> omega

/-- The full packet type determines Zᵣ already in the fine three-row corner;
full spherical maximality is obtained from the identification, not assumed. -/
theorem full_pattern_index {m : ℕ} (hm : 2 ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) (O : OrbitMatrix.ThreeColumnLengthInput c)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output m)
      (ParabolicWeb.Family.source m) w)
    (ha : (packetMatrix m w hw).a = 0) (hs : (packetMatrix m w hw).s = 0)
    (hb : (packetMatrix m w hw).beta = 0) (hd : (packetMatrix m w hw).delta = 1) :
    w = CanonicalSpherical.index m (packetMatrix m w hw).rank := by
  let A := packetMatrix m w hw
  have hz := CanonicalSpherical.index_doubleMaximal A.rank_le c
  apply O.matrix_injective (FiniteBlocks.Family.output hm) rfl w _ hw
    (spherical_supported m A.rank)
  · simpa only [FiniteBlocks.Family.output_index,
      ← FiniteBlocks.Family.source_eq_standard] using hmax
  · rw [FiniteBlocks.Family.output_index,← FiniteBlocks.Family.source_eq_standard]
    exact ⟨fun i hi => hz.1 i (ParabolicWeb.Family.output_source m hi),hz.2⟩
  · funext row col
    rw [OrbitMatrix.compositionEntries_output,OrbitMatrix.compositionEntries_output,
      spherical_entries A.rank_le]
    exact congrFun (congrFun (full_identification A ha hs hb hd) row) col

end Guralnick.PacketIndexClassification
