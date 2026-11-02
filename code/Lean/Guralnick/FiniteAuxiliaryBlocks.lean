import Guralnick.FiniteBlocks
import Guralnick.CanonicalSpherical

/-!
# Normalization of the two auxiliary flag words

All exponents are calculated from positive cyclic compositions. At a unit
packet the zero edge is deleted explicitly, so the j=1 and f=1 cases use
the same actual finite parabolics without zero-size blocks.
-/

noncomputable section
namespace Guralnick.FiniteAuxiliaryBlocks
open ParabolicWeb CanonicalChains

def whole {n : ℕ} (a : Fin n) : FiniteBlocks.Composition n where
  packets := [n]
  positive := by simp; exact Fin.pos a
  total := by simp
  cut := a

def two {n : ℕ} (a : Fin n) (ha : 0 < a.val) : FiniteBlocks.Composition n where
  packets := [a.val,n-a.val]
  positive := by simp; omega
  total := by simp
  cut := ⟨0, by omega⟩

def marked {n : ℕ} (a : Fin n) (ha : 0 < a.val) : FiniteBlocks.Composition n where
  packets := if a.val=1 then [1,n-1] else [1,a.val-1,n-a.val]
  positive := by split_ifs <;> simp <;> omega
  total := by split_ifs <;> simp <;> omega
  cut := ⟨0, by omega⟩

theorem whole_index {n : ℕ} (a : Fin n) : (whole a).index = omitNode a := by
  apply Subtype.ext
  ext i
  have h : (a.val+n)%n=a.val := by simp [Nat.mod_eq_of_lt a.isLt]
  simp [FiniteBlocks.Composition.index, FiniteBlocks.Composition.cuts, whole,
    List.scanl, h, Nat.mod_eq_of_lt a.isLt, omitNode, Fin.ext_iff, -Fin.val_eq_zero_iff]

theorem two_index {n : ℕ} (a : Fin n) (ha : 0 < a.val) :
    (two a ha).index = twoRow (by omega) a := by
  apply Subtype.ext
  ext i
  have hsum : a.val+(n-a.val)=n := by omega
  simp [FiniteBlocks.Composition.index, FiniteBlocks.Composition.cuts, two,
    List.scanl, hsum, Nat.mod_eq_of_lt a.isLt, twoRow, source, omitNode,
    meet, Fin.ext_iff, -Fin.val_eq_zero_iff]
  tauto

theorem marked_index {n : ℕ} (a : Fin n) (ha : 0 < a.val) :
    (marked a ha).index = meet (retainedLine (by omega)) (omitNode a) := by
  have hn : 1<n := by have h:=a.isLt; omega
  have hsum : 1+(a.val-1)=a.val := by omega
  have hsum' : a.val+(n-a.val)=n := by omega
  have hn' : 1+(n-1)=n := by omega
  apply Subtype.ext
  ext i
  by_cases he : a.val=1
  · simp [FiniteBlocks.Composition.index, FiniteBlocks.Composition.cuts, marked,
      he, List.scanl, hn', Nat.mod_eq_of_lt hn, retainedLine, source, omitNode,
      meet, Fin.ext_iff, -Fin.val_eq_zero_iff]
    tauto
  · simp [FiniteBlocks.Composition.index, FiniteBlocks.Composition.cuts, marked,
      he, List.scanl, hsum, hsum', Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt a.isLt,
      retainedLine, source, omitNode, meet, Fin.ext_iff, -Fin.val_eq_zero_iff]
    tauto

theorem retainedLine_eq_two {n : ℕ} (hn : 1<n) :
    retainedLine (by omega) = twoRow (by omega) ⟨1, hn⟩ := by
  apply Subtype.ext
  ext i
  simp [retainedLine, twoRow, source, omitNode, meet, Fin.ext_iff, -Fin.val_eq_zero_iff]

theorem meet_comm (I J : Index n) : meet I J = meet J I := by
  apply Subtype.ext
  exact Finset.inter_comm _ _

theorem line_meet_two {n : ℕ} (hn : 0<n) (a : Fin n) :
    meet (retainedLine hn) (twoRow hn a) = meet (retainedLine hn) (omitNode a) := by
  apply Subtype.ext
  ext i
  simp [retainedLine, twoRow, meet]
  tauto

variable {n : ℕ} {c : Hecke.WindowCoxeter n}
variable (D : ∀ I : Index n, LongestData c I) (hb : FiniteBlocks.BlockLengthInput D)

include hb

theorem whole_length (a : Fin n) :
    2*(c.system.length (D (omitNode a)).longest.val : ℤ) = (n : ℤ)*(n-1) := by
  have h := hb (whole a)
  rw [whole_index] at h
  simpa [FiniteBlocks.Composition.twiceLongestLength, whole] using h

theorem two_length (a : Fin n) (ha : 0<a.val) :
    2*(c.system.length (D (twoRow (by omega) a)).longest.val : ℤ) =
      (a.val : ℤ)*(a.val-1)+((n : ℤ)-a.val)*(n-a.val-1) := by
  have h := hb (two a ha)
  rw [two_index] at h
  simpa [FiniteBlocks.Composition.twiceLongestLength, two,
    Nat.cast_sub (Nat.le_of_lt a.isLt)] using h

theorem marked_length (a : Fin n) (ha : 0<a.val) :
    2*(c.system.length (D (meet (retainedLine (by omega)) (omitNode a))).longest.val : ℤ) =
      ((a.val : ℤ)-1)*(a.val-2)+((n : ℤ)-a.val)*(n-a.val-1) := by
  have h := hb (marked a ha)
  rw [marked_index] at h
  by_cases he : a.val=1
  · simpa [FiniteBlocks.Composition.twiceLongestLength, marked, he,
      Nat.cast_sub (show 1≤n by omega)] using h
  · simp [FiniteBlocks.Composition.twiceLongestLength, marked, he,
      Nat.cast_sub (show 1≤a.val by omega), Nat.cast_sub (Nat.le_of_lt a.isLt)] at h
    nlinarith

theorem oneLine_weight (hn : 0<n) (j f : Fin n) (hj : 0<j.val) (hf : 0<f.val)
    (hs : FiniteBlocks.StandardFiniteLongestInput D) :
    Chain.weight D (oneLineChain hn j f)-c.system.length (AffinePermutation.longest n) =
      2*(j.val : ℤ)*(n-j.val)-((n : ℤ)-f.val-j.val+1) := by
  have hn' : 1<n := by have h:=j.isLt; omega
  have hJ := whole_length D hb j
  have hK := two_length D hb (⟨1, hn'⟩ : Fin n) (by simp)
  rw [←retainedLine_eq_two hn'] at hK
  have hF := two_length D hb f hf
  have hI := two_length D hb j hj
  have hL := marked_length D hb j hj
  have hM := marked_length D hb f hf
  simp only [oneLineChain, Chain.weight]
  rw [show meet (source hn) (omitNode j)=twoRow hn j from rfl,
    meet_comm (omitNode j) (retainedLine hn), line_meet_two, hs]
  norm_num only [Fin.val_mk, Nat.cast_one] at hK
  nlinarith

theorem spherical_weight (hn : 0<n) (s : Fin n)
    (hs : FiniteBlocks.StandardFiniteLongestInput D) :
    Chain.weight D (sphericalChain hn s)-c.system.length (AffinePermutation.longest n) =
      2*(s.val : ℤ)*(n-s.val) := by
  by_cases hs0 : s.val=0
  · have he : s=⟨0, hn⟩ := Fin.ext hs0
    subst s
    simp only [sphericalChain, Chain.weight]
    have hmeet : meet (source hn) (source hn)=source hn := by
      apply Subtype.ext
      exact Finset.inter_self _
    change (_ : ℤ)=2*(0 : ℤ)*(n-0)
    change (c.system.length (D (source hn)).longest.val : ℤ)+
        c.system.length (D (source hn)).longest.val-
        c.system.length (D (meet (source hn) (source hn))).longest.val+
        c.system.length (D (source hn)).longest.val-
        c.system.length (D (meet (source hn) (source hn))).longest.val-
        c.system.length (AffinePermutation.longest n)=_
    rw [hmeet, hs]
    ring
  · have hW := whole_length D hb (⟨0, hn⟩ : Fin n)
    have hJ := whole_length D hb s
    have hI := two_length D hb s (by omega)
    change 2*(c.system.length (D (source hn)).longest.val : ℤ)=_ at hW
    simp only [sphericalChain, Chain.weight]
    rw [meet_comm (omitNode s) (source hn)]
    change (c.system.length (D (source hn)).longest.val : ℤ)+
        c.system.length (D (omitNode s)).longest.val-
        c.system.length (D (twoRow hn s)).longest.val+
        c.system.length (D (source hn)).longest.val-
        c.system.length (D (twoRow hn s)).longest.val-
        c.system.length (AffinePermutation.longest n)=_
    have hw := hs hn
    rw [hw] at hW ⊢
    nlinarith

end Guralnick.FiniteAuxiliaryBlocks
