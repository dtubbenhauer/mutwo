import Guralnick.CanonicalAuxiliarySource
import Guralnick.FiniteAuxiliaryBlocks

/-! # Verified source-degree margins for the auxiliary one-line webs -/
noncomputable section
namespace Guralnick.CanonicalAuxiliaryMargins
open Hecke ParabolicWeb CanonicalChains Positivity CanonicalGallery

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
  (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
  (hblocks : FiniteBlocks.BlockLengthInput D)
  (hsource : FiniteBlocks.StandardFiniteLongestInput D)

include C G hblocks hsource in
/-- Each retained-line source coordinate has minimum degree at least
N−f−j+1. This is proved for the actual integral Hecke word. -/
theorem source_lowerBound (hn : 1<2*m+1) (j f : Fin (2*m+1))
    (hj : 1≤j.val) (hf : 1≤f.val) :
    LowerBound (K.standard.repr (oneLine K D L (Nat.zero_lt_of_lt hn) j f)
      (AffinePermutation.longest (2*m+1))) ((2*m+1 : ℕ)-f.val-j.val+1 : ℤ) := by
  rw [CanonicalAuxiliarySource.one_line_source_coordinate hn j f K D L C G hj hf,
    FiniteAuxiliaryBlocks.oneLine_weight D hblocks (Nat.zero_lt_of_lt hn) j f hj hf hsource]
  have hb := bound_mul (qInt_bound (f.val : ℤ))
    (qGauss_bound ((2*m+1 : ℕ)-1 : ℤ) ((j.val : ℤ)-1))
  have h := normalized_lowerBound
    (2*(j.val : ℤ)*((2*m+1 : ℕ)-j.val)-((2*m+1 : ℕ)-f.val-j.val+1 : ℤ))
    _ _ hb
  convert h using 1 <;> ring

include C G hblocks hsource in
/-- Once the auxiliary web has been identified canonically, its exact
source margin transfers by equality inside the actual Hecke algebra. -/
theorem canonical_source_lowerBound (hn : 1<2*m+1) (j f : Fin (2*m+1))
    (hj : 1≤j.val) (hf : 1≤f.val) (w : AffinePermutation (2*m+1))
    (heq : oneLine K D L (Nat.zero_lt_of_lt hn) j f=K.canonical w) :
    LowerBound (K.standard.repr (K.canonical w) (AffinePermutation.longest (2*m+1)))
      ((2*m+1 : ℕ)-f.val-j.val+1 : ℤ) := by
  rw [← heq]
  exact source_lowerBound K D L C G hblocks hsource hn j f hj hf

include C G hblocks hsource in
/-- Multiplicity allowance l−1 and the strong source margin l+2 leave
three powers of v. Both factors are actual Laurent coefficients. -/
theorem strong_source_product (hm : 2≤m) (j : Fin (2*m+1)) (hj : 1≤j.val)
    (w : AffinePermutation (2*m+1))
    (heq : oneLine K D L (by omega) j ⟨m,by omega⟩=K.canonical w)
    (p : LP) (hp : LowerBound p (-((m : ℤ)-j.val-1))) :
    LowerBound (p*K.standard.repr (K.canonical w) (AffinePermutation.longest (2*m+1))) 3 := by
  have h := lowerBound_mul hp (canonical_source_lowerBound K D L C G hblocks hsource
    (by omega) j ⟨m,by omega⟩ hj (by change 1≤m; omega) w heq)
  convert h using 1 <;> push_cast <;> ring

include C G hblocks hsource in
/-- Multiplicity allowance l−2 and the weak source margin l+1 again give
three powers of v, excluding every weak auxiliary term from [v]. -/
theorem weak_source_product (hm : 2≤m) (j : Fin (2*m+1)) (hj : 1≤j.val)
    (w : AffinePermutation (2*m+1))
    (heq : oneLine K D L (by omega) j ⟨m+1,by omega⟩=K.canonical w)
    (p : LP) (hp : LowerBound p (-((m : ℤ)-j.val-2))) :
    LowerBound (p*K.standard.repr (K.canonical w) (AffinePermutation.longest (2*m+1))) 3 := by
  have h := lowerBound_mul hp (canonical_source_lowerBound K D L C G hblocks hsource
    (by omega) j ⟨m+1,by omega⟩ hj (by change 1≤m+1; omega) w heq)
  convert h using 1 <;> push_cast <;> ring

end Guralnick.CanonicalAuxiliaryMargins
