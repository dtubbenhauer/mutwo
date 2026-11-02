import Guralnick.OrbitMatrixSortedWindows
import Guralnick.FamilyInversions

/-! # The length gap of a supported right-maximal window, counted by pairs

Right maximality orders the inverse residue positions by winding. Each
actual inversion then contributes its finite-source baseline plus one of
three elementary winding comparisons. No orbit dimension theorem is used.
-/
noncomputable section
namespace Guralnick.OrbitDimensionInversions
open Hecke OrbitMatrixElementary
open scoped BigOperators
variable {N : ℕ} [NeZero N]

/-- The source location of an output residue evaluates to that residue
minus its inverse winding. -/
theorem inverse_residue_entry (w : AffinePermutation N) (i : Fin N) :
    w.entry ((w⁻¹).residue i) = (i.val : ℤ)+1-N*(w⁻¹).winding i := by
  simp [AffinePermutation.entry,AffinePermutation.inv_eq_inverse,AffinePermutation.inverse]

/-- Inverse residue order for a decreasing full source window. -/
theorem inverse_residue_lt_iff (w : AffinePermutation N) (hw : StrictAnti w.entry)
    (i j : Fin N) (hij : i<j) :
    (w⁻¹).residue j < (w⁻¹).residue i ↔ (w⁻¹).winding j ≤ (w⁻¹).winding i := by
  have hN : (0 : ℤ)<N := by exact_mod_cast NeZero.pos N
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val<j.val := hij
  have he : w.entry ((w⁻¹).residue i) < w.entry ((w⁻¹).residue j) ↔
      (w⁻¹).residue j < (w⁻¹).residue i := hw.lt_iff_lt
  rw [←he,inverse_residue_entry,inverse_residue_entry]
  constructor
  · intro h
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (show (w⁻¹).winding i+1 ≤ (w⁻¹).winding j by omega)
      (le_of_lt hN)
    push_cast at hi hj
    nlinarith
  · intro h
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt hN)
    omega

/-- Extra inversions beyond one finite-source inversion for an ordered pair. -/
def pairExtra (a b : ℤ) : ℤ :=
  (if a+1<b then 1 else 0) + (if b+1<a then 1 else 0) + (if b<a then 1 else 0)

set_option maxHeartbeats 500000 in
theorem inverse_inversion_pair (w : AffinePermutation N) (hw : StrictAnti w.entry)
    (hs : WindowPacketMatrix.Supported w) (i j : Fin N) (hij : i<j) :
    ((((w⁻¹).entry j-(w⁻¹).entry i)/(N : ℤ)).natAbs : ℤ) =
      1 + pairExtra ((w⁻¹).winding i) ((w⁻¹).winding j) := by
  rw [Int.natCast_natAbs,Family.entry_difference_div (NeZero.pos N)]
  have he := inverse_residue_lt_iff w hw i j hij
  change ((w⁻¹).residue j).val<((w⁻¹).residue i).val ↔ _ at he
  simp only [he]
  have hi := hs i
  have hj := hs j
  have hi' : (w⁻¹).winding i = -1 ∨ (w⁻¹).winding i = 0 ∨ (w⁻¹).winding i = 1 := by omega
  have hj' : (w⁻¹).winding j = -1 ∨ (w⁻¹).winding j = 0 ∨ (w⁻¹).winding j = 1 := by omega
  rcases hi' with hi'|hi'|hi' <;> rcases hj' with hj'|hj'|hj' <;>
    norm_num [hi',hj',pairExtra]

theorem longest_inversion_pair (i j : Fin N) (hij : i<j) :
    ((((AffinePermutation.longest N).entry j-(AffinePermutation.longest N).entry i)/
      (N : ℤ)).natAbs : ℤ)=1 := by
  rw [Family.entry_difference_div (NeZero.pos N)]
  have hrev : ((AffinePermutation.longest N).residue j).val <
      ((AffinePermutation.longest N).residue i).val := by
    change j.rev.val < i.rev.val
    simp only [Fin.val_rev]
    have hi:=i.isLt
    have hj:=j.isLt
    have h : i.val<j.val:=hij
    omega
  simp only [AffinePermutation.longest_winding,Pi.zero_apply,if_pos hrev]
  norm_num

/-- The supported length gap is a finite sum of elementary pair terms. -/
theorem length_gap (c : WindowCoxeter N) (w : AffinePermutation N)
    (hr : ∀ i ∈ (CanonicalChains.source (NeZero.pos N)).val,c.system.IsRightDescent w i)
    (hs : WindowPacketMatrix.Supported w) :
    (c.system.length w : ℤ)-c.system.length (AffinePermutation.longest N) =
      ∑ i : Fin N, ∑ j : Fin N,
        if i<j then pairExtra ((w⁻¹).winding i) ((w⁻¹).winding j) else 0 := by
  rw [←c.system.length_inv w,c.length_formula,c.length_formula]
  simp only [AffinePermutation.inversionCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i<j
  · simp only [if_pos hij,inverse_inversion_pair w (right_maximal_strictAnti c w hr) hs i j hij,
      longest_inversion_pair i j hij]
    ring
  · simp only [if_neg hij,sub_self]

#print axioms length_gap
end Guralnick.OrbitDimensionInversions
