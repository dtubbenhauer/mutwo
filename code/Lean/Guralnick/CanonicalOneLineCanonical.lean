import Guralnick.CanonicalTwoRowWindow
import Guralnick.CanonicalChains

/-! # Canonicality of the actual one-retained-line Hecke word -/
noncomputable section
namespace Guralnick.CanonicalOneLineCanonical
open Hecke ParabolicWeb CanonicalChains CanonicalSchur Positivity
  CanonicalTwoRowMatrix CanonicalTwoRowWindow WindowPacketMatrix

variable {m : ℕ} {c : WindowCoxeter (2*m+1)}

/-- These are the unique zero-degree positions derived from the two-case
count, stated in terms of an actual two-row matrix. -/
def Leading {N f : ℕ} (A : MatrixData N f) (j : ℕ) : Prop :=
  A.rank=j ∧ A.a=1 ∧ ((1≤A.d ∧ A.b=0) ∨ (A.d=0 ∧ A.b=1))

theorem leading_unique (lengths : OrbitMatrix.ThreeColumnLengthInput c)
    (j f : Fin (2*m+1)) (hf : 0<f.val)
    (w t : AffinePermutation (2*m+1)) (hw : Supported w) (ht : Supported t)
    (hwm : DoubleMaximal c (twoRow (by omega) f) (source (by omega)) w)
    (htm : DoubleMaximal c (twoRow (by omega) f) (source (by omega)) t)
    (hwl : Leading (matrix f w hw) j.val) (htl : Leading (matrix f t ht) j.val) : w=t := by
  have he : (matrix f w hw).entry=(matrix f t ht).entry := by
    apply MatrixData.entries_eq_of_parameters _ (Nat.le_of_lt f.isLt)
    · exact hwl.1.trans htl.1.symm
    · exact hwl.2.1.trans htl.2.1.symm
    · rw [(matrix f w hw).leading_b hwl.1 hwl.2.2,
        (matrix f t ht).leading_b htl.1 htl.2.2]
  apply lengths.matrix_injective (FiniteAuxiliaryBlocks.two f hf) rfl w t hw ht
    (by simpa only [FiniteAuxiliaryBlocks.two_index] using hwm)
    (by simpa only [FiniteAuxiliaryBlocks.two_index] using htm)
  funext i k
  rw [composition_entries f hf w,composition_entries f hf t]
  exact congrFun (congrFun he i) k

theorem matrix_feasible (j f : Fin (2*m+1))
    (hjf : j.val≤f.val) (hjnf : j.val≤2*m+1-f.val)
    (w : AffinePermutation (2*m+1)) (h : Supported w)
    (hrj : (matrix f w h).rank≤j.val) :
    1≤(matrix f w h).n ∧ 0≤(j.val : ℤ)-(matrix f w h).rank ∧
      (j.val : ℤ)-(matrix f w h).rank≤(matrix f w h).d ∧
      (j.val : ℤ)-(matrix f w h).rank≤(matrix f w h).n-(matrix f w h).d := by
  have hr := (packetMatrix m w h).rank_le
  rw [← rank_eq f w h] at hr
  have hfN := f.isLt
  unfold MatrixData.n MatrixData.d
  omega

/-- The canonical uniqueness step uses actual standard coordinates and
actual support from galleries. These two premises are original statements
and are discharged by the orbit/convolution calculation, not literature. -/
theorem of_coordinate_formula (K : KLRealization c)
    (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
    (P : PositivityInput K) (S : Compatibility K)
    (lengths : OrbitMatrix.ThreeColumnLengthInput c)
    (j f : Fin (2*m+1)) (hj : 0<j.val) (hf : 0<f.val)
    (hjf : j.val≤f.val) (hjnf : j.val≤2*m+1-f.val)
    (t : AffinePermutation (2*m+1)) (ht : Supported t)
    (htm : DoubleMaximal c (twoRow (by omega) f) (source (by omega)) t)
    (htl : Leading (matrix f t ht) j.val)
    (hsupport : ∀ w, K.standard.repr (oneLine K D L (by omega) j f) w≠0 →
      ∃ hw : Supported w, (matrix f w hw).rank≤j.val)
    (hcoords : ∀ (w : AffinePermutation (2*m+1)) (hw : Supported w),
      DoubleMaximal c (twoRow (by omega) f) (source (by omega)) w →
      K.standard.repr (oneLine K D L (by omega) j f) w =
        normalize (CanonicalOneLine.lengthGap (matrix f w hw).n
          ((j.val : ℤ)-(matrix f w hw).rank) (matrix f w hw).d
          (matrix f w hw).a (matrix f w hw).b)
          (CanonicalAuxiliary.oneLineCount (matrix f w hw).n
            ((j.val : ℤ)-(matrix f w hw).rank) (matrix f w hw).d
            (matrix f w hw).a (matrix f w hw).b)) :
    oneLine K D L (by omega) j f=K.canonical t := by
  apply three_canonical_of_coordinates K D L P S _ _ _ _ t
  · change K.standard.repr (oneLine K D L (by omega) j f) t=1
    rw [hcoords t ht htm,htl.1,sub_self,htl.2.1]
    have hn := (matrix_feasible j f hjf hjnf t ht htl.1.le).1
    simpa only [map_one] using CanonicalAuxiliary.oneLine_leading
      (matrix f t ht).n (matrix f t ht).d (matrix f t ht).b hn htl.2.2
  · intro w hwm hwt
    change LowerBound (K.standard.repr (oneLine K D L (by omega) j f) w) 1
    by_cases hz : K.standard.repr (oneLine K D L (by omega) j f) w=0
    · rw [hz]
      intro k hk
      rfl
    obtain ⟨hw,hrj⟩ := hsupport w hz
    have hfeas := matrix_feasible j f hjf hjnf w hw hrj
    rw [hcoords w hw hwm]
    apply CanonicalAuxiliary.oneLine_proper_positive _ _ _ _ _ hfeas.1 hfeas.2.1
      hfeas.2.2.1 hfeas.2.2.2 (matrix f w hw).a_nonnegative
      (matrix f w hw).b_nonnegative (matrix f w hw).line_feasible
      ((matrix f w hw).quotient_feasible (Nat.le_of_lt f.isLt))
    rintro ⟨hs0,ha,hb⟩
    have hr : (matrix f w hw).rank=j.val := by omega
    exact hwt (leading_unique lengths j f hf w t hw ht hwm htm ⟨hr,ha,hb⟩ htl)

end Guralnick.CanonicalOneLineCanonical
