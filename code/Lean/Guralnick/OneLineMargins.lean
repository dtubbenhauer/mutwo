import Guralnick.OneLineSpecialization

/-! # Uniform contribution bounds for the actual one-line web

The zero-rank cases are checked using the signed Gaussian definition.
All remaining bounds apply to actual standard coefficients and include
the allowed negative degree of the main web's canonical multiplicity.
-/
noncomputable section
namespace Guralnick.OneLineSpecialization
open Hecke ParabolicWeb CanonicalChains WindowPacketMatrix OrbitMatrix
open MainPacketCoordinate CanonicalAuxiliary CanonicalGallery CanonicalCorrection Positivity

/-- Both Gaussian pieces vanish at negative lower rank. -/
theorem count_negative (n s d a b : ℤ) (hs : s<0) : oneLineCount n s d a b=0 := by
  simp [oneLineCount,qGauss,show ¬0≤s by omega,show ¬1≤s by omega]

/-- At a spherical endpoint the zero residual rank also vanishes: the
retained line must enlarge the fixed lower subspace. -/
theorem spherical_count_nonpositive (n s d : ℤ) (hs : s≤0) :
    oneLineCount n s d 0 0=0 := by
  simp [oneLineCount,qGauss,show ¬1≤s by omega]

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
  (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
  (O : CoordinateInput (2*m+1))
  (hblocks : FiniteBlocks.BlockLengthInput D) (hsource : FiniteBlocks.StandardFiniteLongestInput D)

include C G O hblocks hsource

theorem at_marked_invalid {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m ∨ f.val=m+1) (hbad : s.val<r) :
    K.standard.repr (oneLine K D L (by omega) s f) (Guralnick.Family.upper hm hr hrm)=0 := by
  rw [at_marked K D L hm hr hrm s f hs hf C G O hblocks hsource,
    count_negative _ _ _ _ _ (by omega)]
  simp only [normalize,Polynomial.toFinsupp_zero,Finsupp.mapDomain_zero]

theorem at_spherical_invalid {r : ℕ} (hm : 2≤m) (hr : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m ∨ f.val=m+1) (hbad : s.val<r) :
    K.standard.repr (oneLine K D L (by omega) s f) (CanonicalSpherical.index m r)=0 := by
  rw [at_spherical K D L hm hr s f hs hf C G O hblocks hsource,
    count_negative _ _ _ _ _ (by omega)]
  simp only [normalize,Polynomial.toFinsupp_zero,Finsupp.mapDomain_zero]

/-- The full-spherical coefficient vanishes also at equal rank. -/
theorem at_spherical_rank_ge {r : ℕ} (hm : 2≤m) (hr : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m ∨ f.val=m+1) (hbad : s.val≤r) :
    K.standard.repr (oneLine K D L (by omega) s f) (CanonicalSpherical.index m r)=0 := by
  rw [at_spherical K D L hm hr s f hs hf C G O hblocks hsource,
    spherical_count_nonpositive _ _ _ (by omega)]
  simp only [normalize,Polynomial.toFinsupp_zero,Finsupp.mapDomain_zero]

/-- Exact strong lower bound at C_r in the nonempty rank range. -/
theorem strong_at_marked_lowerBound {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m)
    (hrs : r≤s.val) (hsm : s.val<m) :
    LowerBound (K.standard.repr (oneLine K D L (by omega) s f)
      (Guralnick.Family.upper hm hr hrm)) ((m : ℤ)+s.val-2*r+1) := by
  rw [at_marked K D L hm hr hrm s f hs (Or.inl hf) C G O hblocks hsource]
  have hn : 2*(m : ℤ)+1-2*r=2*((m : ℤ)-r)+1 := by ring
  rw [hf,hn]
  apply lowerBound_mono (strong_at_typeF ((m : ℤ)-r) ((s.val : ℤ)-r) (by omega) (by omega))
  omega

/-- Exact weak lower bound at C_r in the nonempty rank range. -/
theorem weak_at_marked_lowerBound {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m+1)
    (hrs : r≤s.val) (hsm : s.val<m) :
    LowerBound (K.standard.repr (oneLine K D L (by omega) s f)
      (Guralnick.Family.upper hm hr hrm)) ((m : ℤ)+s.val-2*r+2) := by
  rw [at_marked K D L hm hr hrm s f hs (Or.inr hf) C G O hblocks hsource]
  have hn : 2*(m : ℤ)+1-2*r=2*((m : ℤ)-r)+1 := by ring
  have hd : (f.val : ℤ)-r=((m : ℤ)-r)+1 := by rw [hf]; push_cast; ring
  rw [hn,hd]
  apply lowerBound_mono (weak_at_typeF ((m : ℤ)-r) ((s.val : ℤ)-r) (by omega) (by omega))
  omega

/-- The manuscript's full strong margin is 2(s-r)+2. -/
theorem strong_at_marked_margin_sharp {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m)
    (hrs : r≤s.val) (hsm : s.val<m)
    {p : LP} (hp : LowerBound p (-((m : ℤ)-s.val-1))) :
    LowerBound (p * K.standard.repr (oneLine K D L (by omega) s f)
      (Guralnick.Family.upper hm hr hrm)) (2*((s.val : ℤ)-r)+2) := by
  have hq := strong_at_marked_lowerBound K D L C G O hblocks hsource
    hm hr hrm s f hs hf hrs hsm
  exact lowerBound_mono (lowerBound_mul hp hq) (by omega)

/-- The manuscript's full weak margin is 2(s-r)+4. -/
theorem weak_at_marked_margin_sharp {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m+1)
    (hrs : r≤s.val) (hsm : s.val<m)
    {p : LP} (hp : LowerBound p (-((m : ℤ)-s.val-2))) :
    LowerBound (p * K.standard.repr (oneLine K D L (by omega) s f)
      (Guralnick.Family.upper hm hr hrm)) (2*((s.val : ℤ)-r)+4) := by
  have hq := weak_at_marked_lowerBound K D L C G O hblocks hsource
    hm hr hrm s f hs hf hrs hsm
  exact lowerBound_mono (lowerBound_mul hp hq) (by omega)

/-- Strong multiplicity allowances cannot contribute to degree zero at a
marked endpoint. The out-of-range branch is proved exactly zero. -/
theorem strong_at_marked_margin {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m) (hsm : s.val<m)
    {p : LP} (hp : LowerBound p (-((m : ℤ)-s.val-1))) :
    LowerBound (p * K.standard.repr (oneLine K D L (by omega) s f)
      (Guralnick.Family.upper hm hr hrm)) 1 := by
  by_cases hbad : s.val<r
  · rw [at_marked_invalid K D L C G O hblocks hsource hm hr hrm s f hs (Or.inl hf) hbad,mul_zero]
    intro z _
    rfl
  · have hq := strong_at_marked_lowerBound K D L C G O hblocks hsource
      hm hr hrm s f hs hf (by omega) hsm
    exact lowerBound_mono (lowerBound_mul hp hq) (by omega)

theorem weak_at_marked_margin {r : ℕ} (hm : 2≤m) (hr : 1≤r) (hrm : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m+1) (hsm : s.val<m)
    {p : LP} (hp : LowerBound p (-((m : ℤ)-s.val-2))) :
    LowerBound (p * K.standard.repr (oneLine K D L (by omega) s f)
      (Guralnick.Family.upper hm hr hrm)) 1 := by
  by_cases hbad : s.val<r
  · rw [at_marked_invalid K D L C G O hblocks hsource hm hr hrm s f hs (Or.inr hf) hbad,mul_zero]
    intro z _
    rfl
  · have hq := weak_at_marked_lowerBound K D L C G O hblocks hsource
      hm hr hrm s f hs hf (by omega) hsm
    exact lowerBound_mono (lowerBound_mul hp hq) (by omega)

/-- Every strong one-line contribution at every Z_r starts at degree three,
including invalid Gaussian ranks. -/
theorem strong_at_spherical_margin (hm : 2≤m) {r : ℕ} (hr : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m)
    {p : LP} (hp : LowerBound p (-((m : ℤ)-s.val-1))) :
    LowerBound (p * K.standard.repr (oneLine K D L (by omega) s f)
      (CanonicalSpherical.index m r)) 3 := by
  rw [at_spherical K D L hm hr s f hs (Or.inl hf) C G O hblocks hsource,hf]
  exact strong_full_spherical_margin m r s.val (by exact_mod_cast hr) hp

theorem weak_at_spherical_margin (hm : 2≤m) {r : ℕ} (hr : r≤m)
    (s f : Fin (2*m+1)) (hs : 1≤s.val) (hf : f.val=m+1)
    {p : LP} (hp : LowerBound p (-((m : ℤ)-s.val-2))) :
    LowerBound (p * K.standard.repr (oneLine K D L (by omega) s f)
      (CanonicalSpherical.index m r)) 3 := by
  rw [at_spherical K D L hm hr s f hs (Or.inr hf) C G O hblocks hsource,hf]
  push_cast
  exact weak_full_spherical_margin m r s.val (by omega) hp

end Guralnick.OneLineSpecialization
