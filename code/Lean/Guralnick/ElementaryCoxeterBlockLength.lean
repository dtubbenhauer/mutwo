import Guralnick.ElementaryCoxeterCyclicCuts
import Guralnick.ElementaryCoxeterOrderedBlocks

/-!
# The finite-parabolic block-length formula, proved from windows

An actual cyclic change of cut sends a parabolic longest window to a
zero-winding permutation. Every omitted boundary preserves its initial
segment, hence every packet. Maximal length forces adjacent descents inside
the packets. Counting the resulting inversions proves the usual sum of
binomial coefficients with no additional literature input.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterBlockLength
open Hecke ParabolicWeb ElementaryCoxeterParabolic ElementaryCoxeterCutLength
open ElementaryCoxeterRotation ElementaryCoxeterPackets ElementaryCoxeterCyclicCuts
open scoped BigOperators

theorem cast_packet_sum (L : List ℕ) :
    (((L.map fun b => b*(b-1)).sum : ℕ) : ℤ)=
      (L.map fun (b : ℕ) => (b : ℤ)*((b : ℤ)-1)).sum := by
  have he (b : ℕ) : ((b*(b-1) : ℕ) : ℤ)=(b : ℤ)*((b : ℤ)-1) := by
    cases b with
    | zero => simp
    | succ b => simp
  induction L with
  | nil => rfl
  | cons b L ih => simpa only [List.map_cons,List.sum_cons,Nat.cast_add,he,ih]

variable {n : ℕ} (c : WindowCoxeter n) (D : ∀ I : Index n, LongestData c I)

/-- The generic cyclic-composition longest-length formula is elementary
from the actual window model and its stated Coxeter length/descent theorem. -/
theorem blockLength : FiniteBlocks.BlockLengthInput D := by
  classical
  intro A
  obtain ⟨L,hpos,htotal,a⟩ := A
  subst n
  let A : FiniteBlocks.Composition L.sum := ⟨L,hpos,rfl,a⟩
  letI : NeZero L.sum := ⟨Nat.ne_of_gt (Fin.pos a)⟩
  let w := rotation a (D A.index).longest.val
  have hwa : (D A.index).longest.val ∈ cutSubgroup a :=
    subgroup_le_cut c A.index a (by
      change a ∉ A.cutsᶜ
      simpa only [Finset.mem_compl,not_not] using A.cut_mem) (D A.index).longest.property
  have hw : w.winding=0 := rotation_zero_winding a _ hwa
  have hcut (r : Fin L.sum) (hr : r.val ∈ L.scanl (·+·) 0) : w ∈ cutSubgroup r := by
    by_cases hr0 : r.val=0
    · intro i
      simp [hw,cutPotential,hr0]
    · have hb : (cutEquiv a).symm r ∉ A.index.val := by
        have hh := (positive_mem_cuts_iff A r (Nat.pos_of_ne_zero hr0)).mpr hr
        exact fun hi => (Finset.mem_compl.mp hi) hh
      have h := rotation_mem_cut c a A.index (D A.index).longest ((cutEquiv a).symm r) hb
      simpa only [Equiv.apply_symm_apply] using h
  have hthreshold (r : Fin L.sum) (hr : r.val ∈ L.scanl (·+·) 0) (i : Fin L.sum) :
      (w.residue i).val<r.val ↔ i.val<r.val := by
    have h := hcut r hr i
    rw [hw] at h
    simp only [Pi.zero_apply,cutPotential] at h
    split_ifs at h <;> omega
  have hpres (i : Fin L.sum) : packet L (w.residue i)=packet L i := by
    apply (packet_eq_iff L _ (packet L i)).mpr
    have hi := packet_spec L i
    have he := prefixSum_end_le L (packet L i)
    constructor
    · by_cases hz : prefixSum L (packet L i)=0
      · omega
      · let r : Fin L.sum := ⟨prefixSum L (packet L i),by have := i.isLt; omega⟩
        have h := hthreshold r (prefixSum_mem_scanl L (packet L i)) i
        change ((w.residue i).val<prefixSum L (packet L i) ↔ i.val<prefixSum L (packet L i)) at h
        omega
    · by_cases ht : prefixSum L (packet L i)+L[(packet L i).val]=L.sum
      · rw [ht]
        exact (w.residue i).isLt
      · let r : Fin L.sum := ⟨prefixSum L (packet L i)+L[(packet L i).val],by omega⟩
        have h := hthreshold r (prefixSum_end_mem_scanl L (packet L i)) i
        exact h.mpr hi.2
  have hdesc (i j : Fin L.sum) (hij : i.val+1=j.val) (hpij : packet L i=packet L j) :
      w.residue j<w.residue i := by
    have hlt : i.val+1<L.sum := by have := j.isLt; omega
    have hadj := adjacent_same_iff L hpos i.val hlt
    have hj : (⟨i.val+1,hlt⟩ : Fin L.sum)=j := Fin.ext hij
    rw [hj] at hadj
    have hs : (cutEquiv a).symm j ∈ A.index.val :=
      (positive_mem_index_iff A j (by omega)).mpr (by simpa only [hij] using hadj.mp hpij)
    have h := ElementaryCoxeterFinite.longest_right_descent c A.index (D A.index)
      ((cutEquiv a).symm j) hs
    have h' := (rotation_right_descent c a (D A.index).longest.val ((cutEquiv a).symm j)).mpr h
    simp only [Equiv.apply_symm_apply] at h'
    change c.system.IsRightDescent w j at h'
    rw [c.finite_descent w i j hij] at h'
    simpa [AffinePermutation.entry,hw] using h'
  have hlen := ElementaryCoxeterOrderedBlocks.twice_length c (Fin.pos a) w hw
    (packet L) (packet_monotone L) hpres hdesc
  have hlen' : 2*c.system.length w=(L.map fun b => b*(b-1)).sum :=
    hlen.trans (by
      convert ordered_pair_count L using 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : packet L i=packet L j ∧ i≠j <;> simp only [h,ite_true,ite_false])
  clear hlen
  have hlen := hlen'
  change 2*c.system.length (rotation a (D A.index).longest.val)=_ at hlen
  rw [rotation_length] at hlen
  have hcast := cast_packet_sum L
  have hc := congrArg (fun z : ℕ => (z : ℤ)) hlen
  dsimp only at hc
  rw [hcast] at hc
  simpa only [Nat.cast_mul,Nat.cast_ofNat,FiniteBlocks.Composition.twiceLongestLength] using hc

#print axioms blockLength
end Guralnick.ElementaryCoxeterBlockLength
