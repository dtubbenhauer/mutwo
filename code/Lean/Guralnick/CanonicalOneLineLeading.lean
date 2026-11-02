import Guralnick.CanonicalOneLineCanonical
import Guralnick.PacketCoarsening
import Guralnick.PacketReflection

/-!
# Actual leading indices of the one-line auxiliary words

The coarse two-row parameters are calculated from the actual inverse-window
counts. The strong and weak support types satisfy the unique leading
condition of the two-case count. Their reflected companions are transported
by the actual affine diagram automorphism.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace Guralnick.CanonicalOneLineLeading
open WindowPacketMatrix CanonicalMatrix CanonicalTwoRowMatrix
  CanonicalTwoRowWindow CanonicalOneLineCanonical

variable {m : ℕ}

theorem entry_m {m : ℕ} (hm : 2 ≤ m) (w : AffinePermutation (2*m+1))
    (row : Fin 2) (col : Fin 3) :
    entry (⟨m,by omega⟩ : Fin (2*m+1)) w row col =
      PacketCoarsening.mergeLast (entries m w) row col := by
  rw [← composition_entries _ (by dsimp; omega)]
  exact congrFun (congrFun (PacketCoarsening.compositionEntries_mergeLast hm w) row) col

theorem entry_m1 {m : ℕ} (hm : 2 ≤ m) (w : AffinePermutation (2*m+1))
    (row : Fin 2) (col : Fin 3) :
    entry (⟨m+1,by omega⟩ : Fin (2*m+1)) w row col =
      PacketCoarsening.mergeFirst (entries m w) row col := by
  rw [← composition_entries _ (by dsimp; omega)]
  exact congrFun (congrFun (PacketCoarsening.compositionEntries_mergeFirst hm w) row) col

/-- All five coarse parameters at the strong auxiliary boundary. -/
theorem parameters_m (hm : 2 ≤ m) (w : AffinePermutation (2*m+1)) (hw : Supported w) :
    let A := packetMatrix m w hw
    let B := matrix (⟨m,by omega⟩ : Fin (2*m+1)) w hw
    B.rank=A.rank ∧ B.n=2*A.corank+1 ∧ B.d=A.corank ∧ B.a=A.a ∧ B.b=A.s := by
  dsimp only
  have hr := rank_eq (⟨m,by omega⟩ : Fin (2*m+1)) w hw
  refine ⟨hr,?_,?_,?_,?_⟩
  · unfold MatrixData.n PacketMatrix.corank
    rw [hr]
    push_cast
    ring
  · unfold MatrixData.d PacketMatrix.corank
    rw [hr]
  · change (entry (⟨m,by omega⟩ : Fin (2*m+1)) w 0 0 : ℤ) = entries m w 0 0
    rw [entry_m hm]
    rfl
  · change (entry (⟨m,by omega⟩ : Fin (2*m+1)) w 1 2 : ℤ) =
      (entries m w 1 2 : ℤ)+entries m w 2 2
    rw [entry_m hm]
    simp [PacketCoarsening.mergeLast]

/-- All five coarse parameters at the weak auxiliary boundary. -/
theorem parameters_m1 (hm : 2 ≤ m) (w : AffinePermutation (2*m+1)) (hw : Supported w) :
    let A := packetMatrix m w hw
    let B := matrix (⟨m+1,by omega⟩ : Fin (2*m+1)) w hw
    B.rank=A.rank ∧ B.n=2*A.corank+1 ∧ B.d=A.corank+1 ∧
      B.a=A.a+A.beta ∧ B.b=A.s+A.delta-1 := by
  dsimp only
  have hr := rank_eq (⟨m+1,by omega⟩ : Fin (2*m+1)) w hw
  refine ⟨hr,?_,?_,?_,?_⟩
  · unfold MatrixData.n PacketMatrix.corank
    rw [hr]
    push_cast
    ring
  · unfold MatrixData.d PacketMatrix.corank
    rw [hr]
    push_cast
    ring
  · change (entry (⟨m+1,by omega⟩ : Fin (2*m+1)) w 0 0 : ℤ) =
      (entries m w 0 0 : ℤ)+entries m w 1 0
    rw [entry_m1 hm]
    simp [PacketCoarsening.mergeFirst]
  · change (entry (⟨m+1,by omega⟩ : Fin (2*m+1)) w 1 2 : ℤ) =
      ((packetMatrix m w hw).s+(packetMatrix m w hw).delta-1)
    rw [entry_m1 hm]
    have hmid := (packetMatrix m w hw).middle_row
    simp only [PacketCoarsening.mergeFirst,Matrix.cons_val_one]
    unfold PacketMatrix.s PacketMatrix.delta
    change (entries m w 2 2 : ℤ) =
      ((entries m w 1 2 : ℤ)+entries m w 2 2)+
        ((entries m w 1 0 : ℤ)+entries m w 1 1)-1
    change entries m w 1 0+entries m w 1 1+entries m w 1 2=1 at hmid
    omega

/-- The strong pattern is the actual leading position at boundary m. -/
theorem strong_leading (hm : 2 ≤ m) (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (ha : (packetMatrix m w hw).a=1) (hs : (packetMatrix m w hw).s=0) :
    Leading (matrix (⟨m,by omega⟩ : Fin (2*m+1)) w hw) (packetMatrix m w hw).rank := by
  obtain ⟨hr,hn,hd,hca,hcb⟩ := parameters_m hm w hw
  refine ⟨hr,hca.trans ha,Or.inl ⟨?_,hcb.trans hs⟩⟩
  have hf := (matrix (⟨m,by omega⟩ : Fin (2*m+1)) w hw).line_feasible
  rw [hca,hcb,ha,hs] at hf
  omega

/-- The weak pattern is the actual leading position at boundary m+1. -/
theorem weak_leading (hm : 2 ≤ m) (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (ha : (packetMatrix m w hw).a=0) (hs : (packetMatrix m w hw).s=0)
    (hb : (packetMatrix m w hw).beta=1) (hd : (packetMatrix m w hw).delta=1) :
    Leading (matrix (⟨m+1,by omega⟩ : Fin (2*m+1)) w hw) (packetMatrix m w hw).rank := by
  obtain ⟨hr,hn,hcd,hca,hcb⟩ := parameters_m1 hm w hw
  have hnon := (packetMatrix m w hw).corank_nonnegative
  refine ⟨hr,?_,Or.inl ⟨?_,?_⟩⟩ <;> omega

/-- The strong pattern cannot occur at the terminal rank. -/
theorem strong_rank_lt (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (ha : (packetMatrix m w hw).a=1) (hs : (packetMatrix m w hw).s=0) :
    (packetMatrix m w hw).rank < m := by
  have h := (packetMatrix m w hw).line_feasible
  rw [ha,hs,add_zero] at h
  unfold PacketMatrix.corank at h
  omega

/-- Rank is positive for either original one-line pattern. -/
theorem rank_positive_of_weak (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hb : (packetMatrix m w hw).beta=1) : 1 ≤ (packetMatrix m w hw).rank := by
  unfold PacketMatrix.beta PacketMatrix.rank at *
  omega

/-- The reflected strong-dual packet has the strong leading parameters. -/
theorem strongDual_leading (hm : 2 ≤ m) (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (ha : (packetMatrix m w hw).a=0) (hs : (packetMatrix m w hw).s=1)
    (hb : (packetMatrix m w hw).beta=0) (hd : (packetMatrix m w hw).delta=1) :
    Leading (matrix (⟨m,by omega⟩ : Fin (2*m+1)) (AffineReflection.reflect w)
      (PacketReflection.supported_reflect hw)) (packetMatrix m w hw).rank := by
  have hp := PacketReflection.parameters_reflect m w hw
  dsimp only at hp
  rw [← PacketReflection.rank_reflect m w hw]
  apply strong_leading hm
  · omega
  · omega

/-- The reflected weak-dual packet has the weak leading parameters. -/
theorem weakDual_leading (hm : 2 ≤ m) (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (ha : (packetMatrix m w hw).a=0) (hs : (packetMatrix m w hw).s=1)
    (hb : (packetMatrix m w hw).beta=0) (hd : (packetMatrix m w hw).delta=0) :
    Leading (matrix (⟨m+1,by omega⟩ : Fin (2*m+1)) (AffineReflection.reflect w)
      (PacketReflection.supported_reflect hw)) (packetMatrix m w hw).rank := by
  have hp := PacketReflection.parameters_reflect m w hw
  dsimp only at hp
  rw [← PacketReflection.rank_reflect m w hw]
  apply weak_leading hm <;> omega

end Guralnick.CanonicalOneLineLeading
