import Guralnick.CanonicalRowSum
import Guralnick.KLFamily
import Guralnick.CanonicalSchur

/-!
# The actual full-spherical affine indices

The unmarked rank-r relative position is the increasing affine translation
with r windings -1, then zeros, then r windings +1. Its upper endpoint is
obtained by the same right multiplication by the finite longest element as
in the desired family. These are actual affine permutations, not arbitrary
labels for correction terms. Clamping only makes the index total outside
its stated range; every theorem uses r≤m.
-/

noncomputable section
namespace Guralnick.CanonicalSpherical

open scoped BigOperators

def translation (m r : ℕ) : AffinePermutation (2*m+1) where
  residue := Equiv.refl _
  winding := Family.winding m (min r m)
  balanced := Family.winding_balanced (Nat.min_le_right r m)

def index (m r : ℕ) : AffinePermutation (2*m+1) :=
  translation m r * AffinePermutation.longest (2*m+1)

theorem translation_winding {m r : ℕ} (hr : r ≤ m) :
    (translation m r).winding = Family.winding m r := by
  simp only [translation, Nat.min_eq_left hr]

theorem index_injective {m r s : ℕ} (hr : r ≤ m) (hs : s ≤ m)
    (he : index m r = index m s) : r=s := by
  have htrans : translation m r = translation m s := mul_right_cancel he
  have hwind := congrArg AffinePermutation.winding htrans
  rw [translation_winding hr, translation_winding hs] at hwind
  have hlt : ∀ a b : ℕ, a ≤ m → b ≤ m → a < b →
      Family.winding m a ≠ Family.winding m b := by
    intro a b ha hb hab habs
    let i : Fin (2*m+1) := ⟨a, by omega⟩
    have h := congrFun habs i
    simp only [Family.winding, i, lt_self_iff_false, if_false, if_pos hab] at h
    have hna : ¬(2*m+1-a ≤ a) := by omega
    rw [if_neg hna] at h
    norm_num at h
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · exact False.elim (hlt r s hr hs hrs hwind)
  · exact hrs
  · exact False.elim (hlt s r hs hr hrs hwind.symm)

theorem index_zero (m : ℕ) : index m 0 = AffinePermutation.longest (2*m+1) := by
  have hz : translation m 0 = 1 := by
    apply AffinePermutation.ext
    · rfl
    · funext i
      have hi := i.isLt
      simp [translation, Family.winding, show ¬(2*m+1 ≤ i.val) by omega]
  simp only [index, hz, one_mul]

/-- A marked family index is different from every unmarked spherical
index: its residue permutation already distinguishes them. -/
theorem family_disjoint {m j r : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    Family.upper hm hj hjm ≠ index m r := by
  intro he
  have htrans : Family.affine hm hj hjm = translation m r := mul_right_cancel he
  let i : Fin (2*m+1) := ⟨j-1, by omega⟩
  have hres := congrArg (fun u : AffinePermutation (2*m+1) => (u.residue i).val) htrans
  have hi : ((Family.residue hm hj hjm i).val : ℤ) = (i.val : ℤ) := by
    exact_mod_cast hres
  rw [Family.residue_value] at hi
  have hsmall : Weights.smallResidue m j i = -1 := by
    simp [Weights.smallResidue, Weights.leftResidue, i, show j-1 < m by omega,
      show j-1+1=j by omega]
  rw [hsmall] at hi
  dsimp only [i] at hi
  omega

def windingValue (m r a : ℕ) : ℤ :=
  if a < r then -1 else if 2*m+1-r ≤ a then 1 else 0

theorem window_eq_range {m r : ℕ} (hr : r ≤ m) :
    (translation m r).window = (List.range (2*m+1)).map
      (fun a : ℕ => (a : ℤ)+1+(2*m+1 : ℕ)*windingValue m r a) := by
  rw [AffinePermutation.window, List.ofFn_eq_map, ← List.map_coe_finRange (2*m+1),
    List.map_map]
  congr 1
  funext i
  simp only [Function.comp_apply, AffinePermutation.entry, translation,
    Equiv.refl_apply, Nat.min_eq_left hr, Family.winding, windingValue]

def matrixInterval (m r : ℕ) (row col : Fin 3) : ℕ × ℕ :=
  match row.val, col.val with
  | 0, 0 => (0,0)
  | 0, 1 => (r,m)
  | 0, _ => (0,r)
  | 1, 0 => (0,0)
  | 1, 1 => (m,m+1)
  | 1, _ => (0,0)
  | _, 0 => (2*m+1-r,2*m+1)
  | _, 1 => (m+1,2*m+1-r)
  | _, _ => (0,0)

theorem entry_inRow {m r a : ℕ} (hr : r ≤ m) (ha : a < 2*m+1)
    (row col : Fin 3) :
    inRow m row ((a : ℤ)+1+(2*m+1 : ℕ)*windingValue m r a +
      (2*m+1 : ℕ)*Family.columnShift col) =
      decide ((matrixInterval m r row col).1 ≤ a ∧ a < (matrixInterval m r row col).2) := by
  fin_cases row <;> fin_cases col <;>
    norm_num [inRow, matrixInterval, Family.columnShift] <;>
    unfold windingValue <;> split_ifs <;> norm_num <;>
    first
    | omega
    | apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

def array (m r : ℕ) : Fin 3 → Fin 3 → ℕ :=
  ![![0,m-r,r], ![0,1,0], ![r,m-r,0]]

/-- The actual block-intersection counts of the unmarked affine translation
are the type-A full-spherical matrix from the six-position classification. -/
theorem matrixEntry_eq_array {m r : ℕ} (hr : r ≤ m) (row col : Fin 3) :
    matrixEntry m (translation m r) row (Family.columnShift col) = array m r row col := by
  unfold matrixEntry
  rw [window_eq_range hr, List.filter_map, List.length_map]
  have hfilter : ((List.range (2*m+1)).filter fun a : ℕ =>
      inRow m row ((a : ℤ)+1+(2*m+1 : ℕ)*windingValue m r a +
        (2*m+1 : ℕ)*Family.columnShift col)) =
      (List.range (2*m+1)).filter fun a => decide
        ((matrixInterval m r row col).1 ≤ a ∧ a < (matrixInterval m r row col).2) := by
    apply List.filter_congr
    intro a ha
    exact entry_inRow hr (List.mem_range.mp ha) row col
  change ((List.range (2*m+1)).filter fun a : ℕ =>
      inRow m row ((a : ℤ)+1+(2*m+1 : ℕ)*windingValue m r a +
        (2*m+1 : ℕ)*Family.columnShift col)).length = _
  rw [hfilter]
  have hbounds : (matrixInterval m r row col).1 ≤ (matrixInterval m r row col).2 ∧
      (matrixInterval m r row col).2 ≤ 2*m+1 := by
    fin_cases row <;> fin_cases col <;> norm_num [matrixInterval] <;> omega
  rw [Family.range_filter_interval _ _ _ hbounds.1,
    min_eq_right hbounds.2, min_eq_right (hbounds.1.trans hbounds.2)]
  fin_cases row <;> fin_cases col <;> norm_num [matrixInterval, array] <;> omega

theorem translation_increasing {m r : ℕ} (hr : r ≤ m) :
    StrictMono (translation m r).entry := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  have hab' : a.val < b.val := hab
  simp only [AffinePermutation.entry, translation, Equiv.refl_apply,
    Nat.min_eq_left hr, Family.winding]
  split_ifs <;> norm_num <;> omega

theorem translation_inversionCount {m r : ℕ} (hr : r ≤ m) :
    ((translation m r).inversionCount : ℤ) = 2*(r : ℤ)*(2*m+1-r) := by
  rw [Family.increasing_inversionCount (by omega) _ (translation_increasing hr)]
  have he : ∀ a b : Fin (2*m+1),
      (if a < b then (translation m r).winding b-(translation m r).winding a -
        (if ((translation m r).residue b).val < ((translation m r).residue a).val
          then 1 else 0) else 0) =
      if a < b then Family.winding m r b-Family.winding m r a else 0 := by
    intro a b
    rw [translation_winding hr]
    simp only [translation, Equiv.refl_apply]
    by_cases hab : a < b
    · simp only [if_pos hab, if_neg (show ¬ b.val < a.val by omega), sub_zero]
    · simp only [if_neg hab]
  simp_rw [he]
  exact Family.winding_difference_sum hr

/-- The full-spherical gap is computed from the actual affine windows. -/
theorem index_length_gap {m r : ℕ} (hr : r ≤ m) (c : Hecke.WindowCoxeter (2*m+1)) :
    (c.system.length (index m r) : ℤ)-c.system.length (AffinePermutation.longest (2*m+1)) =
      2*(r : ℤ)*(2*m+1-r) := by
  rw [c.length_formula, c.length_formula, index,
    Family.reversal_inversion_gap (by omega) _ (translation_increasing hr)]
  exact translation_inversionCount hr

theorem index_inverse (m r : ℕ) : (index m r)⁻¹ = index m r := by
  rw [index, mul_inv_rev, AffinePermutation.longest_inv]
  apply AffinePermutation.ext
  · simp [translation, AffinePermutation.inv_eq_inverse, AffinePermutation.inverse]
  · funext i
    simp only [AffinePermutation.mul_winding, AffinePermutation.longest_winding,
      Pi.zero_apply, zero_add, add_zero, AffinePermutation.longest_residue,
      Fin.revPerm_apply, AffinePermutation.inv_eq_inverse, AffinePermutation.inverse,
      translation, Equiv.refl_symm, Equiv.refl_apply]
    exact (Family.winding_rev (Nat.min_le_right r m) i).symm

theorem index_right_descent {m r : ℕ} (hr : r ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) (b : Fin (2*m+1)) (hb : b.val ≠ 0) :
    c.system.IsRightDescent (index m r) b := by
  let a : Fin (2*m+1) := ⟨b.val-1, by have h := b.isLt; omega⟩
  have hab : a.val+1=b.val := by dsimp [a]; omega
  rw [c.finite_descent _ a b hab, index, AffinePermutation.mul_longest_entry,
    AffinePermutation.mul_longest_entry]
  apply translation_increasing hr
  have ha := a.isLt
  have hb' := b.isLt
  change 2*m+1-(b.val+1) < 2*m+1-(a.val+1)
  omega

theorem index_left_descent {m r : ℕ} (hr : r ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) (b : Fin (2*m+1)) (hb : b.val ≠ 0) :
    c.system.IsLeftDescent (index m r) b := by
  rw [← index_inverse m r, c.system.isLeftDescent_inv_iff]
  exact index_right_descent hr c b hb

/-- These are genuine maximal spherical indices at both boundaries. -/
theorem index_doubleMaximal {m r : ℕ} (hr : r ≤ m)
    (c : Hecke.WindowCoxeter (2*m+1)) :
    CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.source m)
      (ParabolicWeb.Family.source m) (index m r) := by
  constructor
  · intro b hb
    apply index_left_descent hr c b
    exact (Finset.mem_filter.mp hb).2
  · intro b hb
    apply index_right_descent hr c b
    exact (Finset.mem_filter.mp hb).2

/-- The index hypotheses in the descending correction are now discharged
by the explicit affine permutations. -/
theorem correction_indexing (m : ℕ) :
    (∀ r < m-1, ∀ s < m-1, index m r = index m s → r=s) := by
  intro r hr s hs he
  exact index_injective (by omega) (by omega) he

open Hecke ParabolicWeb Positivity CanonicalCorrection CanonicalFullCorrection CanonicalRowSum

/-- Final assembly with the manuscript's actual marked and unmarked affine
indices. The six displayed inputs are remaining ORIGINAL web-coordinate
identities and margins. The indexing, all length gaps, multiplicity one,
canonical correction, Gaussian cancellation and KL readout are proved.
-/
theorem row_sum_of_local_coordinate_identities {m : ℕ} (hm : 2 ≤ m)
    {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
    (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D) (P : PositivityInput K)
    (hcount : ∀ j : Fin m, K.standard.repr (ParabolicWeb.Family.raw K D L) (familyIndex hm j) =
      normalize (CanonicalGallery.gap ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1)
        (CanonicalGallery.count ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1))
    (hauxFamily : ∀ (j : Fin m) w, (∀ k : Fin m, w ≠ familyIndex hm k) →
      LowerBound (K.canonical.repr (ParabolicWeb.Family.raw K D L) w *
        K.standard.repr (K.canonical w) (familyIndex hm j)) 1)
    (hfullRaw : ∀ r < m-1,
      K.standard.repr (ParabolicWeb.Family.raw K D L) (index m r) = rawCoordinate (m-r))
    (htransition : ∀ r < m-1, ∀ s < m-1,
      K.standard.repr (K.canonical (index m s)) (index m r) =
        if r ≤ s then transition (m-r) (s-r) else 0)
    (hnonsphericalAtZ : ∀ r < m-1, ∀ w, (∀ s < m-1, w ≠ index m s) →
      LowerBound (K.canonical.repr (ParabolicWeb.Family.raw K D L) w *
        K.standard.repr (K.canonical w) (index m r)) 1)
    (hauxSource : ∀ w, (∀ j : Fin m, w ≠ familyIndex hm j) →
      (∀ r < m-1, w ≠ index m r) →
      LowerBound (K.canonical.repr (ParabolicWeb.Family.raw K D L) w *
        K.standard.repr (K.canonical w) (AffinePermutation.longest (2*m+1))) 3) :
    (∑ j : Fin m, familyMu hm (show 1 ≤ j.val+1 by omega) (by omega) K) =
      (Nat.choose (m+1) 2 : ℤ) := by
  apply row_sum_of_original_coordinate_obligations K D L P hm (index m)
    (correction_indexing m) (fun j r _ => family_disjoint hm (by omega) (by omega))
    hcount hauxFamily
    (full_residual_positive_of_coordinates K D L (index m) (correction_indexing m)
      hfullRaw htransition hnonsphericalAtZ)
  · simpa only [index_zero, Nat.sub_zero] using hfullRaw 0 (by omega)
  · intro r hr
    simpa only [index_zero, Nat.sub_zero, Nat.zero_le, if_true] using
      htransition 0 (by omega) r hr
  · exact hauxSource
  · intro j
    exact family_length_gap hm (by omega) (by omega) c

end Guralnick.CanonicalSpherical
