import Guralnick.WindowPacketMatrix
import Guralnick.OrbitMatrix

/-! # Cumulative orbit counts read from actual inverse-winding packets -/
noncomputable section
namespace Guralnick.WindowPacketMatrix
open scoped BigOperators
open Classical

/-- Residues in an initial row interval below an inverse-winding cut. -/
def prefixCount {N : ℕ} (w : AffinePermutation N) (b : ℕ) (q : ℤ) : ℕ :=
  (Finset.univ.filter fun i : Fin N => i.val < b ∧ (w⁻¹).winding i < q).card

/-- Enumerate an integer interval in the principal period by actual residues. -/
theorem interval_residue_count {N : ℕ} (a b : ℕ) (hab : a ≤ b) (hbN : b ≤ N)
    (P : ℤ → Prop) [DecidablePred P] :
    ((Finset.Ioc (a : ℤ) (b : ℤ)).filter P).card =
      (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b ∧ P (i.val+1)).card := by
  symm
  apply Finset.card_bij (fun i _ => (i.val : ℤ)+1)
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
    simp only [Finset.mem_filter,Finset.mem_Ioc]
    exact ⟨by omega,hi.2.2⟩
  · intro i hi j hj heq
    apply Fin.ext
    omega
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_Ioc] at hx
    let i : Fin N := ⟨(x-1).toNat,by omega⟩
    have heq : (i.val : ℤ)+1 = x := by dsimp [i]; omega
    refine ⟨i,?_,heq⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [heq]
    dsimp [i]
    exact ⟨by omega,by omega,hx.2⟩

/-- The residue lies in 1..N, so an entry is at or below period q exactly
when its winding is strictly below q. -/
theorem entry_le_period {N : ℕ} [NeZero N] (w : AffinePermutation N)
    (i : Fin N) (q : ℤ) : w.entry i ≤ (N : ℤ)*q ↔ w.winding i < q := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hr := (w.residue i).isLt
  constructor
  · intro h
    by_contra hn
    have hh : q ≤ w.winding i := by omega
    have hh' := mul_le_mul_of_nonneg_left hh hN.le
    unfold AffinePermutation.entry at h
    omega
  · intro h
    have hh : w.winding i ≤ q-1 := by omega
    have hh' := mul_le_mul_of_nonneg_left hh hN.le
    unfold AffinePermutation.entry
    nlinarith

theorem inverse_integer_entry {N : ℕ} [NeZero N] (w : AffinePermutation N) (i : Fin N) :
    w.onIntegers.symm ((i.val : ℤ)+1) = (w⁻¹).entry i := by
  rw [← OrbitMatrix.onIntegers_inv N w]
  simpa only [mul_zero,add_zero] using OrbitMatrix.onIntegers_packet N (w⁻¹) i 0

/-- The generic cumulative integer count is exactly the finite inverse-winding count. -/
theorem cumulative_eq_prefix {N : ℕ} [NeZero N] (w : AffinePermutation N)
    (b : ℕ) (hbN : b ≤ N) (q : ℤ) :
    OrbitMatrix.cumulativeCount N w 0 b ((N : ℤ)*q) = prefixCount w b q := by
  unfold OrbitMatrix.cumulativeCount prefixCount
  have h := interval_residue_count 0 b (Nat.zero_le _) hbN
    (fun x => w.onIntegers.symm x ≤ (N : ℤ)*q)
  simp only [Nat.cast_zero,Nat.zero_le,true_and] at h
  refine h.trans ?_
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Nat.zero_le, true_and]
  rw [inverse_integer_entry,entry_le_period]

theorem entry_period_interval {N : ℕ} [NeZero N] (w : AffinePermutation N)
    (i : Fin N) (q : ℤ) :
    ((N : ℤ)*q < w.entry i ∧ w.entry i ≤ (N : ℤ)*q+N) ↔ w.winding i = q := by
  have hlow : (N : ℤ)*q < w.entry i ↔ q ≤ w.winding i := by
    rw [← not_le,entry_le_period]
    omega
  have he : (N : ℤ)*(q+1) = (N : ℤ)*q+N := by ring
  rw [hlow,← he,entry_le_period]
  omega

/-- Actual orbit blocks within the principal target period count precisely
residues of the given inverse winding. No support restriction is needed. -/
theorem blockCount_residues {N : ℕ} [NeZero N] (w : AffinePermutation N)
    (a b : ℕ) (hab : a ≤ b) (hbN : b ≤ N) (q : ℤ) :
    OrbitMatrix.blockCount N w a b ((N : ℤ)*q) ((N : ℤ)*q+N) =
      (Finset.univ.filter fun i : Fin N =>
        a ≤ i.val ∧ i.val < b ∧ (w⁻¹).winding i = q).card := by
  unfold OrbitMatrix.blockCount
  have h := interval_residue_count a b hab hbN
    (fun x => (N : ℤ)*q < w.onIntegers.symm x ∧ w.onIntegers.symm x ≤ (N : ℤ)*q+N)
  refine h.trans ?_
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [inverse_integer_entry,entry_period_interval]

def rowLower (m : ℕ) (row : Fin 3) : ℕ := ![0,m,m+1] row
def rowUpper (m : ℕ) (row : Fin 3) : ℕ := ![m,m+1,2*m+1] row

theorem rowOf_interval (m : ℕ) (i : Fin (2*m+1)) (row : Fin 3) :
    rowOf m i = row ↔ rowLower m row ≤ i.val ∧ i.val < rowUpper m row := by
  fin_cases row
  · change rowOf m i = 0 ↔ 0 ≤ i.val ∧ i.val < m
    rw [rowOf_zero]
    omega
  · change rowOf m i = 1 ↔ m ≤ i.val ∧ i.val < m+1
    rw [rowOf_one]
    omega
  · change rowOf m i = 2 ↔ m+1 ≤ i.val ∧ i.val < 2*m+1
    rw [rowOf_two]
    have hi := i.isLt
    omega

/-- The original translated-window block count equals the independent
output-residue inverse-winding count. This fixes the source packet and all
column signs, rather than merely comparing displayed numeric matrices. -/
theorem matrixEntry_eq_inverse_count (m : ℕ) (w : AffinePermutation (2*m+1))
    (row : Fin 3) (q : ℤ) :
    matrixEntry m w row q =
      (Finset.univ.filter fun i : Fin (2*m+1) => rowOf m i = row ∧ (w⁻¹).winding i = q).card := by
  letI : NeZero (2*m+1) := ⟨by omega⟩
  have hab : rowLower m row ≤ rowUpper m row := by
    fin_cases row <;> simp [rowLower,rowUpper] <;> omega
  have hbN : rowUpper m row ≤ 2*m+1 := by
    fin_cases row <;> simp [rowUpper] <;> omega
  have hlow : (rowLower m row : ℤ) = OrbitMatrix.familyRowLower m row := by
    fin_cases row <;> simp [rowLower,OrbitMatrix.familyRowLower]
  have hupp : (rowUpper m row : ℤ) = OrbitMatrix.familyRowUpper m row := by
    fin_cases row <;> simp [rowUpper,OrbitMatrix.familyRowUpper]
  have h := blockCount_residues w (rowLower m row) (rowUpper m row) hab hbN q
  rw [hlow,hupp,OrbitMatrix.blockCount_eq_matrixEntry] at h
  rw [h]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,rowOf_interval]
  tauto

theorem entries_eq_matrixEntry (m : ℕ) (w : AffinePermutation (2*m+1)) (row col : Fin 3) :
    entries m w row col = matrixEntry m w row (Family.columnShift col) :=
  (matrixEntry_eq_inverse_count m w row (Family.columnShift col)).symm

theorem prefix_m_zero (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    prefixCount w m 0 = entries m w 0 0 := by
  simp only [prefixCount,entries,card_filter_sum,rowOf_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hs i
  norm_num [Family.columnShift]
  split_ifs <;> omega

theorem prefix_middle_zero (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    prefixCount w (m+1) 0 = entries m w 0 0 + entries m w 1 0 := by
  simp only [prefixCount,entries,card_filter_sum,rowOf_zero,rowOf_one]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hs i
  norm_num [Family.columnShift]
  split_ifs <;> omega

theorem prefix_N_zero (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    prefixCount w (2*m+1) 0 = entries m w 0 0 + entries m w 1 0 + entries m w 2 0 := by
  rw [column_sum]
  simp only [prefixCount,card_filter_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hs i
  have hil := i.isLt
  norm_num [Family.columnShift]
  split_ifs <;> omega

theorem prefix_m_one (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    prefixCount w m 1 = entries m w 0 0 + entries m w 0 1 := by
  simp only [prefixCount,entries,card_filter_sum,rowOf_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hs i
  norm_num [Family.columnShift]
  split_ifs <;> omega

theorem prefix_middle_one (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    prefixCount w (m+1) 1 =
      entries m w 0 0 + entries m w 0 1 + entries m w 1 0 + entries m w 1 1 := by
  simp only [prefixCount,entries,card_filter_sum,rowOf_zero,rowOf_one]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hs i
  norm_num [Family.columnShift]
  split_ifs <;> omega

theorem prefix_N_one (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    prefixCount w (2*m+1) 1 =
      2*m+1 - (entries m w 0 0 + entries m w 1 0 + entries m w 2 0) := by
  have hsum : prefixCount w (2*m+1) 1 +
      (Finset.univ.filter fun i => (w⁻¹).winding i = 1).card = 2*m+1 := by
    simp only [prefixCount,card_filter_sum]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin (2*m+1), 1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := hs i
        have hil := i.isLt
        split_ifs <;> omega
      _ = 2*m+1 := by simp
  rw [column_sum]
  have he := balanced_packets m w hs
  norm_num [Family.columnShift]
  omega

theorem cumulative_rank (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    OrbitMatrix.cumulativeCount (2*m+1) w 0 (2*m+1) 0 = (packetMatrix m w hs).rank := by
  letI : NeZero (2*m+1) := ⟨by omega⟩
  have h := cumulative_eq_prefix w (2*m+1) (le_refl _) 0
  simp only [mul_zero] at h
  push_cast at h
  rw [h,prefix_N_zero m w hs]
  rfl

theorem cumulative_corank (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    OrbitMatrix.cumulativeCount (2*m+1) w 0 (2*m+1) (2*m+1) =
      2*m+1-(packetMatrix m w hs).rank := by
  letI : NeZero (2*m+1) := ⟨by omega⟩
  have h := cumulative_eq_prefix w (2*m+1) (le_refl _) 1
  simp only [mul_one] at h
  push_cast at h
  rw [h,prefix_N_one m w hs]
  rfl

theorem cumulative_a (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    (OrbitMatrix.cumulativeCount (2*m+1) w 0 m 0 : ℤ) = (packetMatrix m w hs).a := by
  letI : NeZero (2*m+1) := ⟨by omega⟩
  have h := cumulative_eq_prefix w m (by omega) 0
  simp only [mul_zero] at h
  push_cast at h
  rw [h,prefix_m_zero m w hs]
  rfl

theorem cumulative_b (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    (OrbitMatrix.cumulativeCount (2*m+1) w 0 (m+1) 0 : ℤ) =
      (packetMatrix m w hs).a+(packetMatrix m w hs).beta := by
  letI : NeZero (2*m+1) := ⟨by omega⟩
  have h := cumulative_eq_prefix w (m+1) (by omega) 0
  simp only [mul_zero] at h
  push_cast at h
  rw [h,prefix_middle_zero m w hs]
  simp [CanonicalMatrix.PacketMatrix.a,CanonicalMatrix.PacketMatrix.beta,packetMatrix]

theorem cumulative_c (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    (OrbitMatrix.cumulativeCount (2*m+1) w 0 m (2*m+1) : ℤ) =
      (packetMatrix m w hs).corank+(packetMatrix m w hs).s := by
  letI : NeZero (2*m+1) := ⟨by omega⟩
  have h := cumulative_eq_prefix w m (by omega) 1
  simp only [mul_one] at h
  push_cast at h
  rw [h,prefix_m_one m w hs]
  have hrow := (packetMatrix m w hs).first_row
  have hcol := (packetMatrix m w hs).outer_columns
  simp only [CanonicalMatrix.PacketMatrix.corank,CanonicalMatrix.PacketMatrix.s,
    CanonicalMatrix.PacketMatrix.rank,packetMatrix] at *
  omega

theorem cumulative_d (m : ℕ) (w : AffinePermutation (2*m+1)) (hs : Supported w) :
    (OrbitMatrix.cumulativeCount (2*m+1) w 0 (m+1) (2*m+1) : ℤ) =
      (packetMatrix m w hs).corank+(packetMatrix m w hs).s+(packetMatrix m w hs).delta := by
  letI : NeZero (2*m+1) := ⟨by omega⟩
  have h := cumulative_eq_prefix w (m+1) (by omega) 1
  simp only [mul_one] at h
  push_cast at h
  rw [h,prefix_middle_one m w hs]
  have hrow := (packetMatrix m w hs).first_row
  have hcol := (packetMatrix m w hs).outer_columns
  simp only [CanonicalMatrix.PacketMatrix.corank,CanonicalMatrix.PacketMatrix.s,
    CanonicalMatrix.PacketMatrix.rank,CanonicalMatrix.PacketMatrix.delta,packetMatrix] at *
  omega

end Guralnick.WindowPacketMatrix
