import Guralnick.CanonicalSphericalEvaluation
import Guralnick.CanonicalSphericalDifference

/-! # The full-spherical canonical transition, modulo generic literature only -/
noncomputable section
namespace Guralnick.CanonicalSphericalTransition
open scoped BigOperators
open Hecke ParabolicWeb CanonicalChains CanonicalSchur CanonicalSphericalExpansion

variable {m : ℕ} (hm : 2≤m) {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
  (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
  (input : ∀ (k : Type) [Field k], OrbitMatrix.CoordinateDimensionInput k (2*m+1))
  (hblocks : FiniteBlocks.BlockLengthInput D)
  (hsource : FiniteBlocks.StandardFiniteLongestInput D)

include hm C G input hblocks hsource in
/-- The zero-rank word is checked algebraically, so no positive-rank gallery
argument is applied outside its range. -/
theorem raw_standard_all (s r : ℕ) (hs : s≤m) (hr : r≤s) :
    K.standard.repr (raw K D L s hs) (CanonicalSpherical.index m r) =
      CanonicalAuxiliary.sphericalCoefficient (2*m+1-2*r) (s-r) := by
  by_cases hs0 : s=0
  · subst s
    have hr0 : r=0 := by omega
    subst r
    simp only [raw,spherical_zero,symmetrizer,CanonicalSpherical.index_zero,
      Nat.mul_zero,Nat.sub_zero]
    rw [hsource,K.canonical_diagonal]
    unfold CanonicalAuxiliary.sphericalCoefficient
    simp only [Nat.zero_mul,Nat.cast_zero,mul_zero,Gaussian.qBinomial_zero_right]
    change (1 : Positivity.LP) = Finsupp.mapDomain (fun k : ℕ => (0 : ℤ)-2*k) (Finsupp.single 0 1)
    rw [Finsupp.mapDomain_single]
    rfl
  · exact CanonicalSphericalEvaluation.standard_coordinate hm K D L C G input
      hblocks hsource s r (by omega) hs hr

include hm C G input hblocks hsource in
/-- The ordinary standard coordinate of C_Zs at Z_r is the exact normalized
Gaussian difference used in the manuscript's descending correction. All
special spherical support and multiplicity claims have now been proved. -/
theorem canonical_transition (P : PositivityInput K) (S : Compatibility K)
    (lengths : OrbitMatrix.ThreeColumnLengthInput c)
    (s r : ℕ) (hs : s≤m) (hr : r≤s) :
    K.standard.repr (K.canonical (CanonicalSpherical.index m s)) (CanonicalSpherical.index m r) =
      CanonicalFullCorrection.transition (m-r) (s-r) := by
  by_cases hsr : s=r
  · subst s
    rw [K.canonical_diagonal,Nat.sub_self,CanonicalFullCorrection.transition_zero]
  · have hs0 : s≠0 := by omega
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hrt : r≤t := by omega
    have hp := CanonicalSphericalEvaluation.raw_canonical_sum hm K D L C G input
      P S lengths hblocks hsource t (by omega)
    have hn := CanonicalSphericalEvaluation.raw_canonical_sum hm K D L C G input
      P S lengths hblocks hsource (t+1) hs
    rw [canonical_eq_difference K D L t hs hp hn]
    rw [_root_.map_sub K.standard.repr]
    simp only [Finsupp.sub_apply]
    rw [raw_standard_all hm K D L C G input hblocks hsource (t+1) r hs hr,
      raw_standard_all hm K D L C G input hblocks hsource t r (by omega) hrt,
      show 2*m+1-2*r=2*(m-r)+1 by omega,show t+1-r=(t-r)+1 by omega]
    exact CanonicalSphericalDifference.consecutive (m-r) (t-r) (by omega)

/-- Ordinary Bruhat triangularity supplies the other half of the transition
matrix. The strict length comparison is computed from actual Z-windows. -/
theorem canonical_zero_above (s r : ℕ) (hs : s≤m) (hr : r≤m) (hsr : s<r) :
    K.standard.repr (K.canonical (CanonicalSpherical.index m s)) (CanonicalSpherical.index m r)=0 := by
  by_contra hn
  obtain ⟨a,b,hab,hred,ha,hb⟩ := K.canonical_support _ _ hn
  have hlen : c.system.length (CanonicalSpherical.index m r) ≤
      c.system.length (CanonicalSpherical.index m s) := by
    rw [← ha,← hb]
    exact (c.system.length_wordProd_le a).trans (hab.length_le.trans hred.ge)
  have hrl := CanonicalSpherical.index_length_gap hr c
  have hsl := CanonicalSpherical.index_length_gap hs c
  have hp : 0<((r : ℤ)-s)*(2*m+1-r-s) := mul_pos (by omega) (by omega)
  have hlen' : (c.system.length (CanonicalSpherical.index m r) : ℤ) ≤
      c.system.length (CanonicalSpherical.index m s) := by exact_mod_cast hlen
  nlinarith

include hm C G input hblocks hsource in
/-- The complete triangular transition required by the descending
full-spherical correction, with no original coefficient assumptions. -/
theorem transition_matrix (P : PositivityInput K) (S : Compatibility K)
    (lengths : OrbitMatrix.ThreeColumnLengthInput c)
    (s r : ℕ) (hs : s≤m) (hr : r≤m) :
    K.standard.repr (K.canonical (CanonicalSpherical.index m s)) (CanonicalSpherical.index m r) =
      if r≤s then CanonicalFullCorrection.transition (m-r) (s-r) else 0 := by
  split_ifs with hrs
  · exact canonical_transition hm K D L C G input hblocks hsource P S lengths s r hs hrs
  · exact canonical_zero_above K s r hs hr (by omega)

end Guralnick.CanonicalSphericalTransition
