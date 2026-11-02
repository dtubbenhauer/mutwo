import Guralnick.CanonicalSphericalExpansion
import Guralnick.OrbitLengthInput
import Guralnick.PacketCumulative
import Guralnick.FamilyUpperMatrix

/-! # Classification of the actual three-column spherical support -/
noncomputable section
namespace Guralnick.CanonicalSphericalSupport
open scoped BigOperators
open Hecke ParabolicWeb CanonicalSchur WindowPacketMatrix OrbitMatrix

variable {m : ℕ}

theorem index_supported (r : ℕ) : Supported (CanonicalSpherical.index m r) := by
  intro i
  rw [CanonicalSpherical.index_inverse]
  simp only [CanonicalSpherical.index,AffinePermutation.mul_winding,
    AffinePermutation.longest_winding,Pi.zero_apply,add_zero,
    CanonicalSpherical.translation,Family.winding]
  split_ifs <;> norm_num

theorem index_entries (r : ℕ) (hr : r≤m) (row col : Fin 3) :
    entries m (CanonicalSpherical.index m r) row col = CanonicalSpherical.array m r row col := by
  rw [entries_eq_matrixEntry,CanonicalSpherical.index,matrixEntry_mul_longest]
  exact CanonicalSpherical.matrixEntry_eq_array hr row col

/-- The one-row matrix is forced by balance to consist of r,N−2r,r. -/
theorem one_row_entries (hm : 2≤m) (w : AffinePermutation (2*m+1))
    (h : Supported w) (row : Fin 1) (col : Fin 3) :
    compositionEntries (FiniteBlocks.Family.source hm) w row col =
      ![(packetMatrix m w h).rank, 2*m+1-2*(packetMatrix m w h).rank,
        (packetMatrix m w h).rank] col := by
  rw [compositionEntries_source,← column_sum]
  have h0 := (packetMatrix m w h).first_row
  have h1 := (packetMatrix m w h).middle_row
  have h2 := (packetMatrix m w h).last_row
  have he := (packetMatrix m w h).outer_columns
  simp only [packetMatrix] at h0 h1 h2 he
  fin_cases col
  · rfl
  · change entries m w 0 1 + entries m w 1 1 + entries m w 2 1 =
      2*m+1-2*(entries m w 0 0 + entries m w 1 0 + entries m w 2 0)
    omega
  · change entries m w 0 2 + entries m w 1 2 + entries m w 2 2 =
      entries m w 0 0 + entries m w 1 0 + entries m w 2 0
    omega

theorem index_rank (r : ℕ) (hr : r≤m) :
    (packetMatrix m (CanonicalSpherical.index m r) (index_supported r)).rank = r := by
  change entries m (CanonicalSpherical.index m r) 0 0 +
    entries m (CanonicalSpherical.index m r) 1 0 +
    entries m (CanonicalSpherical.index m r) 2 0 = r
  rw [index_entries r hr,index_entries r hr,index_entries r hr]
  simp [CanonicalSpherical.array]

/-- Actual spherical maximal representatives in bounded support are exactly
Z_r, with r read from their actual window. Only generic orbit injectivity
is used; the family classification is proved here. -/
theorem spherical_classification (hm : 2≤m) {c : WindowCoxeter (2*m+1)}
    (input : ThreeColumnLengthInput c) (w : AffinePermutation (2*m+1))
    (h : Supported w)
    (hmax : DoubleMaximal c (CanonicalChains.source (by omega))
      (CanonicalChains.source (by omega)) w) :
    w = CanonicalSpherical.index m (packetMatrix m w h).rank := by
  let r := (packetMatrix m w h).rank
  have hr : r≤m := (packetMatrix m w h).rank_le
  apply input.matrix_injective (FiniteBlocks.Family.source hm) rfl w
    (CanonicalSpherical.index m r) h (index_supported r)
  · simpa only [FiniteBlocks.Family.source_index,FiniteBlocks.Family.source_eq_standard] using hmax
  · simpa only [FiniteBlocks.Family.source_index,← FiniteBlocks.Family.source_eq_standard] using
      CanonicalSpherical.index_doubleMaximal hr c
  · funext row col
    rw [one_row_entries hm w h row col,
      one_row_entries hm (CanonicalSpherical.index m r) (index_supported r) row col,
      index_rank r hr]

end Guralnick.CanonicalSphericalSupport
