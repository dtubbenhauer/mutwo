import Guralnick.CanonicalTwoRowMatrix
import Guralnick.FiniteAuxiliaryBlocks
import Guralnick.OrbitLengthInput
import Guralnick.PacketCumulative

/-! # Actual inverse-window counts for an arbitrary two-row boundary -/
noncomputable section
namespace Guralnick.CanonicalTwoRowWindow
open scoped BigOperators
open Classical WindowPacketMatrix CanonicalTwoRowMatrix
variable {m : ℕ}

def entry (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (row : Fin 2) (col : Fin 3) : ℕ :=
  (Finset.univ.filter fun i : Fin (2*m+1) =>
    (if row=0 then i.val < f.val else f.val ≤ i.val) ∧
      (w⁻¹).winding i=Family.columnShift col).card

theorem row_sum (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w)
    (row : Fin 2) : entry f w row 0+entry f w row 1+entry f w row 2 =
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        if row=0 then i.val < f.val else f.val ≤ i.val).card := by
  simp only [entry,card_filter_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := h i
  have hw : (w⁻¹).winding i = -1 ∨ (w⁻¹).winding i=0 ∨ (w⁻¹).winding i=1 := by omega
  rcases hw with hw | hw | hw <;> simp only [Family.columnShift] <;>
    split_ifs <;> simp_all

theorem column_sum (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (col : Fin 3) :
    entry f w 0 col+entry f w 1 col =
      (Finset.univ.filter fun i => (w⁻¹).winding i=Family.columnShift col).card := by
  simp only [entry,card_filter_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hf : i.val < f.val <;>
    by_cases hw : (w⁻¹).winding i=Family.columnShift col <;> simp [hf,hw,show f.val ≤ i.val ↔ ¬ i.val < f.val by omega]

def matrix (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    MatrixData (2*m+1) f.val where
  entry := entry f w
  first_row := by
    rw [row_sum f w h]
    have he : (Finset.univ.filter fun i : Fin (2*m+1) =>
        if (0 : Fin 2)=0 then i.val < f.val else f.val ≤ i.val) = Finset.Iio f := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,ite_true,Finset.mem_Iio,Fin.lt_def]
    rw [he,Fin.card_Iio]
  last_row := by
    rw [row_sum f w h]
    have he : (Finset.univ.filter fun i : Fin (2*m+1) =>
        if (1 : Fin 2)=0 then i.val < f.val else f.val ≤ i.val) = Finset.Ici f := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ici,Fin.le_def]
      norm_num
    rw [he,Fin.card_Ici]
  balance := by
    rw [column_sum,column_sum]
    exact balanced_packets m w h

theorem rank_eq (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    (matrix f w h).rank = (packetMatrix m w h).rank := by
  change entry f w 0 0+entry f w 1 0 = entries m w 0 0+entries m w 1 0+entries m w 2 0
  rw [column_sum,WindowPacketMatrix.column_sum]

theorem composition_entries (f : Fin (2*m+1)) (hf : 0<f.val)
    (w : AffinePermutation (2*m+1)) (row : Fin 2) (col : Fin 3) :
    OrbitMatrix.compositionEntries (FiniteAuxiliaryBlocks.two f hf) w row col = entry f w row col := by
  unfold OrbitMatrix.compositionEntries entry
  congr 1
  ext i
  fin_cases row <;> simp [FiniteAuxiliaryBlocks.two,i.isLt] <;> omega

theorem prefix_zero (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    prefixCount w f.val 0 = entry f w 0 0 := by
  simp only [prefixCount,entry,card_filter_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := h i
  norm_num [Family.columnShift]
  split_ifs <;> omega

theorem prefix_one (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    prefixCount w f.val 1 = entry f w 0 0+entry f w 0 1 := by
  simp only [prefixCount,entry,card_filter_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := h i
  norm_num [Family.columnShift]
  split_ifs <;> omega

theorem cumulative_a (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    (OrbitMatrix.cumulativeCount (2*m+1) w 0 f.val 0 : ℤ) = (matrix f w h).a := by
  have he := cumulative_eq_prefix w f.val (Nat.le_of_lt f.isLt) 0
  simp only [mul_zero] at he
  rw [he,prefix_zero f w h]
  rfl

theorem cumulative_c (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    (OrbitMatrix.cumulativeCount (2*m+1) w 0 f.val (2*m+1 : ℕ) : ℤ) =
      (matrix f w h).d+(matrix f w h).b := by
  have he := cumulative_eq_prefix w f.val (Nat.le_of_lt f.isLt) 1
  simp only [mul_one] at he
  rw [he,prefix_one f w h]
  have hrow := (matrix f w h).first_row
  have hbal := (matrix f w h).balance
  change entry f w 0 0+entry f w 0 1+entry f w 0 2=f.val at hrow
  change entry f w 0 0+entry f w 1 0=entry f w 0 2+entry f w 1 2 at hbal
  change ((entry f w 0 0+entry f w 0 1 : ℕ) : ℤ) =
    (f.val : ℤ)-(entry f w 0 0+entry f w 1 0 : ℕ)+entry f w 1 2
  omega

theorem cumulative_rank (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    OrbitMatrix.cumulativeCount (2*m+1) w 0 (2*m+1 : ℕ) 0 = (matrix f w h).rank := by
  rw [rank_eq]
  push_cast
  exact WindowPacketMatrix.cumulative_rank m w h

theorem cumulative_corank (f : Fin (2*m+1)) (w : AffinePermutation (2*m+1)) (h : Supported w) :
    OrbitMatrix.cumulativeCount (2*m+1) w 0 (2*m+1 : ℕ) (2*m+1 : ℕ) =
      2*m+1-(matrix f w h).rank := by
  rw [rank_eq]
  push_cast
  exact WindowPacketMatrix.cumulative_corank m w h

theorem actual_dimension {c : Hecke.WindowCoxeter (2*m+1)}
    (lengths : OrbitMatrix.ThreeColumnLengthInput c) (f : Fin (2*m+1)) (hf : 0<f.val)
    (w : AffinePermutation (2*m+1)) (h : Supported w)
    (hmax : CanonicalSchur.DoubleMaximal c (CanonicalChains.twoRow (by omega) f)
      (CanonicalChains.source (by omega)) w) :
    PeriodicMatrix.dimension (fun i j => ((matrix f w h).entry i j : ℤ)) =
      (c.system.length w : ℤ)-c.system.length (AffinePermutation.longest (2*m+1)) := by
  have hd := lengths.dimension_length (FiniteAuxiliaryBlocks.two f hf) rfl w h
    (by simpa only [FiniteAuxiliaryBlocks.two_index] using hmax)
  have he : (fun i j => ((matrix f w h).entry i j : ℤ)) =
      (fun i j => (OrbitMatrix.compositionEntries (FiniteAuxiliaryBlocks.two f hf) w i j : ℤ)) := by
    funext i j
    exact_mod_cast (composition_entries f hf w i j).symm
  rw [he]
  exact hd

theorem actual_normalization {c : Hecke.WindowCoxeter (2*m+1)}
    (D : ∀ I : ParabolicWeb.Index (2*m+1), ParabolicWeb.LongestData c I)
    (lengths : OrbitMatrix.ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D)
    (j f : Fin (2*m+1)) (hj : 0<j.val) (hf : 0<f.val)
    (w : AffinePermutation (2*m+1)) (h : Supported w)
    (hmax : CanonicalSchur.DoubleMaximal c (CanonicalChains.twoRow (by omega) f)
      (CanonicalChains.source (by omega)) w) :
    CanonicalChains.Chain.weight D (CanonicalChains.oneLineChain (by omega) j f) -
      c.system.length w =
      CanonicalOneLine.lengthGap (matrix f w h).n ((j.val : ℤ)-(matrix f w h).rank)
        (matrix f w h).d (matrix f w h).a (matrix f w h).b := by
  have hc := FiniteAuxiliaryBlocks.oneLine_weight D hblocks (show 0<2*m+1 by omega)
    j f hj hf hsource
  have hd := actual_dimension lengths f hf w h hmax
  have ha := (matrix f w h).normalization_gap (Nat.le_of_lt f.isLt) (j.val : ℤ)
  rw [hd] at ha
  linarith

end Guralnick.CanonicalTwoRowWindow
