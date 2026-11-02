import Guralnick.FamilyInversions

/-!
# The actual length gap before applying the Coxeter literature theorem

Reversal of an increasing affine window adds the inversion count of the
finite longest element. The final gap is proved from actual window sums.
-/
namespace Guralnick.Family
open scoped BigOperators

private theorem inversionCount_int {n : ℕ} (w : AffinePermutation n) :
    (w.inversionCount : ℤ) = ∑ i : Fin n, ∑ k : Fin n,
      if i < k then |(w.entry k-w.entry i)/(n : ℤ)| else 0 := by
  simp only [AffinePermutation.inversionCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero, Int.natCast_natAbs]

private theorem sum_rev {n : ℕ} (f : Fin n → ℤ) :
    (∑ i : Fin n, f i.rev) = ∑ i : Fin n, f i := by
  simpa only [Fin.revPerm_apply] using Equiv.sum_comp Fin.revPerm f

private theorem sum_rev_two {n : ℕ} (f : Fin n → Fin n → ℤ) :
    (∑ i : Fin n, ∑ k : Fin n, f i.rev k.rev) =
      ∑ i : Fin n, ∑ k : Fin n, f i k := by
  calc
    _ = ∑ i : Fin n, ∑ k : Fin n, f i.rev k :=
      Finset.sum_congr rfl (fun i _ => sum_rev (f i.rev))
    _ = _ := sum_rev (fun i => ∑ k, f i k)

private theorem reversed_inversionCount {n : ℕ} (w : AffinePermutation n) :
    ((w * AffinePermutation.longest n).inversionCount : ℤ) =
      ∑ i : Fin n, ∑ k : Fin n,
        if i < k then |(w.entry i-w.entry k)/(n : ℤ)| else 0 := by
  rw [inversionCount_int]
  simp only [AffinePermutation.mul_longest_entry]
  have hrev : ∀ i k : Fin n, i < k ↔ k.rev < i.rev := by
    intro i k
    have hi := i.isLt
    have hk := k.isLt
    simp only [Fin.lt_def, Fin.val_rev]
    omega
  calc
    _ = ∑ i : Fin n, ∑ k : Fin n,
        if k.rev < i.rev then |(w.entry k.rev-w.entry i.rev)/(n : ℤ)| else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      simp only [← hrev i k]
    _ = ∑ i : Fin n, ∑ k : Fin n,
        if k < i then |(w.entry k-w.entry i)/(n : ℤ)| else 0 :=
      sum_rev_two (fun i k => if k < i then |(w.entry k-w.entry i)/(n : ℤ)| else 0)
    _ = _ := Finset.sum_comm

private theorem opposite_division_sum {n : ℕ} (hn : 0 < n)
    (w : AffinePermutation n) (a b : Fin n) (hab : a ≠ b) :
    (w.entry b-w.entry a)/(n : ℤ) +
      (w.entry a-w.entry b)/(n : ℤ) = -1 := by
  rw [entry_difference_div hn, entry_difference_div hn]
  have hne : (w.residue a).val ≠ (w.residue b).val := by
    intro h
    exact hab (w.residue.injective (Fin.ext h))
  split_ifs <;> omega

private theorem reversed_pair {n : ℕ} (hn : 0 < n)
    (w : AffinePermutation n) (hw : StrictMono w.entry)
    (a b : Fin n) (hab : a < b) :
    |(w.entry a-w.entry b)/(n : ℤ)| =
      |(w.entry b-w.entry a)/(n : ℤ)|+1 := by
  have hpos := hw hab
  have hdiv := opposite_division_sum hn w a b (ne_of_lt hab)
  have hp : 0 ≤ (w.entry b-w.entry a)/(n : ℤ) :=
    Int.ediv_nonneg (by omega) (by omega)
  have hm : (w.entry a-w.entry b)/(n : ℤ) ≤ 0 := by omega
  rw [abs_of_nonpos hm, abs_of_nonneg hp]
  omega

private theorem longest_entry_difference {n : ℕ} (a b : Fin n) :
    (AffinePermutation.longest n).entry b -
      (AffinePermutation.longest n).entry a = (a.val : ℤ)-b.val := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [AffinePermutation.entry, AffinePermutation.longest_residue,
    AffinePermutation.longest_winding, Pi.zero_apply, mul_zero, add_zero,
    Fin.revPerm_apply, Fin.val_rev]
  omega

private theorem longest_inversionCount {n : ℕ} (hn : 0 < n) :
    ((AffinePermutation.longest n).inversionCount : ℤ) =
      ∑ a : Fin n, ∑ b : Fin n, if a < b then (1 : ℤ) else 0 := by
  rw [inversionCount_int]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : a < b
  · simp only [if_pos hab, longest_entry_difference]
    have ha' := a.isLt
    have hb' := b.isLt
    have hab' : a.val < b.val := hab
    have hnz : (n : ℤ) ≠ 0 := by omega
    have hz : ((a.val : ℤ)-b.val+n*1)/(n : ℤ) = 0 :=
      Int.ediv_eq_zero_of_lt (by omega) (by omega)
    rw [Int.add_mul_ediv_left _ _ hnz] at hz
    have hd : ((a.val : ℤ)-b.val)/(n : ℤ) = -1 := by omega
    rw [hd]
    norm_num
  · simp only [if_neg hab]

/-- For any increasing affine window, multiplying by the finite reversal adds
exactly the finite longest element's inversion count. -/
theorem reversal_inversion_gap {n : ℕ} (hn : 0 < n)
    (w : AffinePermutation n) (hw : StrictMono w.entry) :
    ((w * AffinePermutation.longest n).inversionCount : ℤ) -
      (AffinePermutation.longest n).inversionCount = w.inversionCount := by
  rw [reversed_inversionCount, longest_inversionCount hn, inversionCount_int,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : a < b
  · simp only [if_pos hab, reversed_pair hn w hw a b hab]
    omega
  · simp only [if_neg hab, sub_zero]

/-- The precise family gap, calculated from the two actual affine windows. -/
theorem upper_inversion_gap {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) :
    ((upper hm hj hjm).inversionCount : ℤ) -
      (AffinePermutation.longest (2*m+1)).inversionCount = gapFormula m j := by
  rw [upper, reversal_inversion_gap (by omega) _ (entry_strictMono hm hj hjm)]
  exact affine_inversionCount hm hj hjm

end Guralnick.Family
