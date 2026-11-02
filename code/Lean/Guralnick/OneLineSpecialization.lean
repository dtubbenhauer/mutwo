import Guralnick.OneLineCoordinate
import Guralnick.MainFamilyCoordinate

/-! # One-line coordinates at the marked and spherical affine windows

These identities use the actual retained-line word and actual ordinary
standard indices. The extra power at a marked endpoint is derived from
its length, so no implicit change to a coarse maximal index occurs.
-/
noncomputable section
namespace Guralnick.OneLineSpecialization
open Hecke ParabolicWeb CanonicalChains WindowPacketMatrix OrbitMatrix
open MainPacketCoordinate CanonicalAuxiliary Positivity

variable {m : ℕ}

/-- Coarsening either middle cut in a matrix whose middle particle stays
in the central column preserves the two one-line marks. -/
theorem middle_parameters (w : AffinePermutation (2*m+1)) (hs : Supported w)
    (f : Fin (2*m+1)) (hf : f.val=m ∨ f.val=m+1)
    (hb : (packetMatrix m w hs).beta=0) (hd : (packetMatrix m w hs).delta=1) :
    (CanonicalTwoRowWindow.matrix f w hs).rank=(packetMatrix m w hs).rank ∧
      (CanonicalTwoRowWindow.matrix f w hs).a=(packetMatrix m w hs).a ∧
      (CanonicalTwoRowWindow.matrix f w hs).b=(packetMatrix m w hs).s := by
  refine ⟨CanonicalTwoRowWindow.rank_eq f w hs,?_,?_⟩
  · rw [← CanonicalTwoRowWindow.cumulative_a f w hs]
    rcases hf with hf | hf
    · rw [hf]
      exact cumulative_a m w hs
    · rw [hf]
      have hh := cumulative_b m w hs
      rw [hb,add_zero] at hh
      simpa only [Nat.cast_add,Nat.cast_one] using hh
  · have hc := CanonicalTwoRowWindow.cumulative_c f w hs
    have hR := CanonicalTwoRowWindow.rank_eq f w hs
    unfold CanonicalTwoRowMatrix.MatrixData.d at hc
    rw [hR] at hc
    generalize hvalue : (CanonicalTwoRowWindow.matrix f w hs).b = bb at hc ⊢
    rcases hf with hf | hf
    · rw [hf] at hc
      have hh := cumulative_c m w hs
      unfold CanonicalMatrix.PacketMatrix.corank at hh
      push_cast at hc
      omega
    · rw [hf] at hc
      have hh := cumulative_d m w hs
      rw [hd] at hh
      unfold CanonicalMatrix.PacketMatrix.corank at hh
      push_cast at hc
      omega

theorem marked_parameters {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (hs : Supported (Guralnick.Family.upper hm hr hrm))
    (f : Fin (2*m+1)) (hf : f.val=m ∨ f.val=m+1) :
    let A := CanonicalTwoRowWindow.matrix f (Guralnick.Family.upper hm hr hrm) hs
    A.rank=r ∧ A.n=(2*(m : ℤ)+1-2*r) ∧ A.d=(f.val : ℤ)-r ∧ A.a=1 ∧ A.b=1 := by
  obtain ⟨hR,hl,ha,hS,hb,hd⟩ := MainFamilyCoordinate.marked_parameters hm hr hrm hs
  obtain ⟨hR',ha',hb'⟩ := middle_parameters _ hs f hf hb hd
  dsimp only
  refine ⟨hR'.trans hR,?_,?_,ha'.trans ha,hb'.trans hS⟩
  · unfold CanonicalTwoRowMatrix.MatrixData.n
    rw [hR',hR]
    push_cast
    ring
  · unfold CanonicalTwoRowMatrix.MatrixData.d
    rw [hR',hR]

theorem spherical_parameters {r : ℕ} (hr : r≤m)
    (hs : Supported (CanonicalSpherical.index m r))
    (f : Fin (2*m+1)) (hf : f.val=m ∨ f.val=m+1) :
    let A := CanonicalTwoRowWindow.matrix f (CanonicalSpherical.index m r) hs
    A.rank=r ∧ A.n=(2*(m : ℤ)+1-2*r) ∧ A.d=(f.val : ℤ)-r ∧ A.a=0 ∧ A.b=0 := by
  obtain ⟨hR,hl,ha,hS,hb,hd⟩ := MainFamilyCoordinate.spherical_parameters hr hs
  obtain ⟨hR',ha',hb'⟩ := middle_parameters _ hs f hf hb hd
  dsimp only
  refine ⟨hR'.trans hR,?_,?_,ha'.trans ha,hb'.trans hS⟩
  · unfold CanonicalTwoRowMatrix.MatrixData.n
    rw [hR',hR]
    push_cast
    ring
  · unfold CanonicalTwoRowMatrix.MatrixData.d
    rw [hR',hR]

variable {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)

/-- Exact extra unit of exponent at a marked ordinary endpoint. -/
theorem marked_exponent {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : 1≤f.val)
    (hblocks : FiniteBlocks.BlockLengthInput D) (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    Chain.weight D (oneLineChain (by omega) s f)-c.system.length (Guralnick.Family.upper hm hr hrm) =
      CanonicalOneLine.lengthGap (2*(m : ℤ)+1-2*r) ((s.val : ℤ)-r) ((f.val : ℤ)-r) 1 1+1 := by
  have hw := FiniteAuxiliaryBlocks.oneLine_weight D hblocks (show 0<2*m+1 by omega) s f hs hf hsource
  have hl := Hecke.family_length_gap hm hr hrm c
  unfold gapFormula at hl
  unfold CanonicalOneLine.lengthGap CanonicalOneLine.codimension
  push_cast at hw
  nlinarith

theorem spherical_exponent {r : ℕ} (hr : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : 1≤f.val)
    (hblocks : FiniteBlocks.BlockLengthInput D) (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    Chain.weight D (oneLineChain (by omega) s f)-c.system.length (CanonicalSpherical.index m r) =
      CanonicalOneLine.lengthGap (2*(m : ℤ)+1-2*r) ((s.val : ℤ)-r) ((f.val : ℤ)-r) 0 0 := by
  have hw := FiniteAuxiliaryBlocks.oneLine_weight D hblocks (show 0<2*m+1 by omega) s f hs hf hsource
  have hl := CanonicalSpherical.index_length_gap hr c
  unfold CanonicalOneLine.lengthGap CanonicalOneLine.codimension
  push_cast at hw
  nlinarith

/-- Exact one-line raw standard coordinate at every marked endpoint,
including negative s-r Gaussian indices. -/
theorem at_marked {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m ∨ f.val=m+1)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1))
    (hblocks : FiniteBlocks.BlockLengthInput D) (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    K.standard.repr (oneLine K D L (by omega) s f) (Guralnick.Family.upper hm hr hrm) =
      normalize (CanonicalOneLine.lengthGap (2*(m : ℤ)+1-2*r)
        ((s.val : ℤ)-r) ((f.val : ℤ)-r) 1 1+1)
        (oneLineCount (2*(m : ℤ)+1-2*r) ((s.val : ℤ)-r) ((f.val : ℤ)-r) 1 1) := by
  let hw := Guralnick.Family.upper_supported hm hr hrm
  have hfpos : 1≤f.val := by omega
  have hc := OneLineCoordinate.raw_coordinate K D L (show 1<2*m+1 by omega)
    s f hs hfpos C G O (Guralnick.Family.upper hm hr hrm) hw
  dsimp only at hc
  rw [marked_exponent D hm hr hrm s f hs hfpos hblocks hsource] at hc
  obtain ⟨hR,hn,hd,ha,hb⟩ := marked_parameters hm hr hrm hw f hf
  simpa only [hR,hn,hd,ha,hb] using hc

/-- Exact one-line raw standard coordinate at every unmarked spherical
endpoint, again with signed Gaussian indices and no omitted rank range. -/
theorem at_spherical (hm : 2≤m) {r : ℕ} (hr : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m ∨ f.val=m+1)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : CoordinateInput (2*m+1))
    (hblocks : FiniteBlocks.BlockLengthInput D) (hsource : FiniteBlocks.StandardFiniteLongestInput D) :
    K.standard.repr (oneLine K D L (by omega) s f) (CanonicalSpherical.index m r) =
      normalize (CanonicalOneLine.lengthGap (2*(m : ℤ)+1-2*r)
        ((s.val : ℤ)-r) ((f.val : ℤ)-r) 0 0)
        (oneLineCount (2*(m : ℤ)+1-2*r) ((s.val : ℤ)-r) ((f.val : ℤ)-r) 0 0) := by
  let hw := MainFamilyCoordinate.spherical_supported (m := m) r
  have hfpos : 1≤f.val := by omega
  have hc := OneLineCoordinate.raw_coordinate K D L (show 1<2*m+1 by omega)
    s f hs hfpos C G O (CanonicalSpherical.index m r) hw
  dsimp only at hc
  rw [spherical_exponent D hr s f hs hfpos hblocks hsource] at hc
  obtain ⟨hR,hn,hd,ha,hb⟩ := spherical_parameters hr hw f hf
  simpa only [hR,hn,hd,ha,hb] using hc

end Guralnick.OneLineSpecialization
