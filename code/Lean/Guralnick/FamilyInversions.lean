import Guralnick.FamilyMatrix
import Guralnick.AffineGroup
import Guralnick.Normalization
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Direct inversion sums for the affine family

All sums here are calculated from the actual window entries and residue
permutation. No Coxeter-length value is assumed.
-/
namespace Guralnick.Family
open scoped BigOperators

private theorem sum_range_interval (n a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.range n, if a ≤ i ∧ i < b then (1 : ℤ) else 0) =
      (min n b : ℤ) - min n a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

/-- Counting an interval of residue positions, with integer-valued indicators. -/
theorem sum_fin_interval (n a b : ℕ) (hab : a ≤ b) :
    (∑ i : Fin n, if a ≤ i.val ∧ i.val < b then (1 : ℤ) else 0) =
      (min n b : ℤ) - min n a := by
  calc
    _ = ∑ i ∈ Finset.range n, if a ≤ i ∧ i < b then (1 : ℤ) else 0 :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => if a ≤ i ∧ i < b then (1 : ℤ) else 0) n
    _ = _ := sum_range_interval n a b hab

private theorem sum_fin_lt (n b : ℕ) :
    (∑ i : Fin n, if i.val < b then (1 : ℤ) else 0) = min n b := by
  simpa using sum_fin_interval n 0 b (Nat.zero_le b)

/-- Weighted ordered-pair differences are a single linear sum. -/
theorem ordered_difference_sum {n : ℕ} (f : Fin n → ℤ) :
    (∑ i : Fin n, ∑ k : Fin n,
      if i < k then f k - f i else 0) =
      ∑ i : Fin n, (2*(i.val : ℤ) - n + 1)*f i := by
  have hsplit : ∀ i k : Fin n,
      (if i < k then f k-f i else 0) =
        (if i.val < k.val then f k else 0) -
          (if i.val < k.val then f i else 0) := by
    intro i k
    change (if i.val < k.val then f k-f i else 0) = _
    by_cases h : i.val < k.val <;> simp [h]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i k : Fin n => if i.val < k.val then f k else 0)]
  have hleft : ∀ k : Fin n,
      (∑ i : Fin n, if i.val < k.val then f k else 0) = (k.val : ℤ)*f k := by
    intro k
    calc
      _ = (∑ i : Fin n, if i.val < k.val then (1 : ℤ) else 0)*f k := by
        rw [Finset.sum_mul]
        congr 1
        funext i
        split_ifs <;> simp
      _ = _ := by rw [sum_fin_lt, min_eq_right (Nat.le_of_lt k.isLt)]
  have hright : ∀ i : Fin n,
      (∑ k : Fin n, if i.val < k.val then f i else 0) =
        ((n : ℤ)-i.val-1)*f i := by
    intro i
    calc
      _ = (∑ k : Fin n,
          if i.val+1 ≤ k.val ∧ k.val < n then (1 : ℤ) else 0)*f i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := k.isLt
        split_ifs <;> simp_all <;> omega
      _ = _ := by
        rw [sum_fin_interval _ _ _ i.isLt, min_self,
          min_eq_right i.isLt]
        push_cast
        ring
  simp_rw [hleft, hright]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Euclidean division of two window entries separates winding from the
ordinary residue inversion. -/
theorem entry_difference_div {n : ℕ} (hn : 0 < n) (w : AffinePermutation n)
    (a b : Fin n) :
    (w.entry b - w.entry a)/(n : ℤ) =
      w.winding b-w.winding a -
        (if (w.residue b).val < (w.residue a).val then 1 else 0) := by
  have hnz : (n : ℤ) ≠ 0 := by omega
  have ha := (w.residue a).isLt
  have hb := (w.residue b).isLt
  have heq : w.entry b-w.entry a =
      (((w.residue b).val : ℤ)-(w.residue a).val) +
        n*(w.winding b-w.winding a) := by
    simp only [AffinePermutation.entry]
    ring
  rw [heq, Int.add_mul_ediv_left _ _ hnz]
  by_cases h : (w.residue b).val < (w.residue a).val
  · have hz :
        ((((w.residue b).val : ℤ)-(w.residue a).val) + n*1)/(n : ℤ) = 0 :=
      Int.ediv_eq_zero_of_lt (by omega) (by omega)
    rw [Int.add_mul_ediv_left _ _ hnz] at hz
    simp only [h, ↓reduceIte]
    omega
  · have hz : (((w.residue b).val : ℤ)-(w.residue a).val)/(n : ℤ) = 0 :=
      Int.ediv_eq_zero_of_lt (by omega) (by omega)
    simp [h,hz]

/-- For an increasing window, the inversion expression has no absolute-value
ambiguity. This identity is for the actual window, not a prescribed length. -/
theorem increasing_inversionCount {n : ℕ} (hn : 0 < n)
    (w : AffinePermutation n) (hw : StrictMono w.entry) :
    (w.inversionCount : ℤ) =
      ∑ i : Fin n, ∑ k : Fin n,
        if i < k then w.winding k-w.winding i -
          (if (w.residue k).val < (w.residue i).val then 1 else 0) else 0 := by
  simp only [AffinePermutation.inversionCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero, Int.natCast_natAbs]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hik : i < k
  · simp only [if_pos hik]
    rw [abs_of_nonneg (Int.ediv_nonneg (by have h := hw hik; omega) (by omega)),
      entry_difference_div hn]
  · simp only [if_neg hik]

/-- The two exceptional residue positions. -/
def leftMark {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) : Fin (2*m+1) :=
  ⟨j-1, by omega⟩

def rightMark {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) : Fin (2*m+1) :=
  ⟨2*m+1-j, by omega⟩

set_option maxHeartbeats 1500000 in
/-- Every residue inversion is in one of three disjoint rectangles, two of
which are a marked position against an interval. -/
theorem residue_inversion_indicator {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (a b : Fin (2*m+1)) :
    (if a < b then
      (if ((affine hm hj hjm).residue b).val < ((affine hm hj hjm).residue a).val
        then (1 : ℤ) else 0) else 0) =
    (if a = leftMark hj hjm then
      (if j ≤ b.val ∧ b.val < m+1 then 1 else 0) else 0) +
    (if a = leftMark hj hjm then
      (if b = rightMark hj hjm then 1 else 0) else 0) +
    (if b = rightMark hj hjm then
      (if m ≤ a.val ∧ a.val < 2*m+1-j then 1 else 0) else 0) := by
  have ha := a.isLt
  have hb := b.isLt
  have hza := residue_value hm hj hjm a
  have hzb := residue_value hm hj hjm b
  change ((residue hm hj hjm a).val : ℤ) = _ at hza
  change ((residue hm hj hjm b).val : ℤ) = _ at hzb
  change (if a < b then
    (if (residue hm hj hjm b).val < (residue hm hj hjm a).val then _ else _) else _) = _
  simp only [Fin.ext_iff, leftMark, rightMark, Fin.lt_def]
  unfold Weights.smallResidue Weights.leftResidue at hza hzb
  split_ifs at hza hzb <;> split_ifs <;> omega

/-- There are exactly `2(m-j)+3` ordinary inversions of the residue permutation. -/
theorem residue_inversion_sum {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) :
    (∑ a : Fin (2*m+1), ∑ b : Fin (2*m+1),
      if a < b then
        (if ((affine hm hj hjm).residue b).val < ((affine hm hj hjm).residue a).val
          then (1 : ℤ) else 0) else 0) =
      2*((m : ℤ)-j)+3 := by
  simp_rw [residue_inversion_indicator hm hj hjm, Finset.sum_add_distrib,
    Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero]
  rw [sum_fin_interval _ _ _ (by omega : j ≤ m+1),
    sum_fin_interval _ _ _ (by omega : m ≤ 2*m+1-j)]
  omega

private theorem sum_initial {n j : ℕ} (hjn : j ≤ n) (f : ℕ → ℤ) :
    (∑ i : Fin n, if i.val < j then f i.val else 0) =
      ∑ i ∈ Finset.range j, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then f i else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem twice_sum_range (j : ℕ) :
    2*(∑ i ∈ Finset.range j, (i : ℤ)) = (j : ℤ)*(j-1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

/-- The arithmetic progression contributed by the first `j` windings. -/
theorem initial_linear_sum {n j : ℕ} (hjn : j ≤ n) :
    (∑ i : Fin n, if i.val < j then (n : ℤ)-1-2*i.val else 0) =
      (j : ℤ)*(n-j) := by
  rw [sum_initial hjn (fun i : ℕ => (n : ℤ)-1-2*i)]
  simp only [Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have h := twice_sum_range j
  nlinarith

/-- The winding part of the actual affine inversion sum. -/
theorem winding_difference_sum {m j : ℕ} (hjm : j ≤ m) :
    (∑ a : Fin (2*m+1), ∑ b : Fin (2*m+1),
      if a < b then winding m j b-winding m j a else 0) =
      2*(j : ℤ)*(2*m+1-j) := by
  rw [ordered_difference_sum]
  let f : Fin (2*m+1) → ℤ := fun i =>
    if i.val < j then (2*m+1 : ℕ)-1-2*(i.val : ℤ) else 0
  have hterm : ∀ i : Fin (2*m+1),
      (2*(i.val : ℤ) - (2*m+1 : ℕ) + 1)*winding m j i = f i + f i.rev := by
    intro i
    have hi := i.isLt
    simp only [f, winding, Fin.val_rev, Nat.add_sub_add_right]
    split_ifs <;> simp only [mul_neg_one, mul_one, mul_zero, zero_add, add_zero]
    all_goals omega
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hrev := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (2*m+1))) f
  simp only [Fin.revPerm_apply] at hrev
  rw [hrev]
  have hf : ∑ i, f i = (j : ℤ)*((2*m+1 : ℕ)-j) :=
    initial_linear_sum (by omega)
  rw [hf]
  push_cast
  ring

/-- Direct computation of the affine inversion expression of the increasing
window. Its equality with Coxeter length is the separate general theorem. -/
theorem affine_inversionCount {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) :
    ((affine hm hj hjm).inversionCount : ℤ) = gapFormula m j := by
  rw [increasing_inversionCount (by omega) _ (entry_strictMono hm hj hjm)]
  have hsplit : ∀ a b : Fin (2*m+1),
      (if a < b then (affine hm hj hjm).winding b - (affine hm hj hjm).winding a -
        (if ((affine hm hj hjm).residue b).val < ((affine hm hj hjm).residue a).val
          then (1 : ℤ) else 0) else 0) =
      (if a < b then winding m j b-winding m j a else 0) -
        (if a < b then
          (if ((affine hm hj hjm).residue b).val < ((affine hm hj hjm).residue a).val
            then (1 : ℤ) else 0) else 0) := by
    intro a b
    change (if a < b then winding m j b-winding m j a - _ else 0) = _
    by_cases h : a < b <;> simp [h]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [winding_difference_sum hjm, residue_inversion_sum hm hj hjm]
  unfold gapFormula
  ring

end Guralnick.Family
