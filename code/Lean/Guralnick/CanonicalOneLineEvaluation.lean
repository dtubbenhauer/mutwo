import Guralnick.CanonicalOneLineCanonical
import Guralnick.OneLineCoordinate

/-! # The actual one-line canonicality theorem modulo generic literature -/
noncomputable section
namespace Guralnick.CanonicalOneLineEvaluation
open Hecke ParabolicWeb CanonicalChains CanonicalSchur WindowPacketMatrix
  CanonicalOneLineCanonical CanonicalTwoRowWindow

/-- The one-line Hecke web is canonical. The leading-index premise is an
explicit actual matrix check; the count, support, degree estimates and
canonical correction are all conclusions of the formal proof. -/
theorem canonical_of_leading {m : ℕ} (hm : 2≤m) {c : WindowCoxeter (2*m+1)}
    (K : KLRealization c) (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
    (P : PositivityInput K) (S : Compatibility K)
    (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
    (O : MainPacketCoordinate.CoordinateInput (2*m+1))
    (Q : OrbitMatrix.ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D)
    (j f : Fin (2*m+1)) (hj : 1≤j.val) (hf : 1≤f.val)
    (hjf : j.val≤f.val) (hjnf : j.val≤2*m+1-f.val)
    (t : AffinePermutation (2*m+1)) (ht : Supported t)
    (htm : DoubleMaximal c (twoRow (by omega) f) (source (by omega)) t)
    (htl : Leading (matrix f t ht) j.val) :
    oneLine K D L (by omega) j f=K.canonical t := by
  apply of_coordinate_formula K D L P S Q j f hj hf hjf hjnf t ht htm htl
  · intro w hw
    exact OneLineCoordinate.support_and_rank K D L (by omega) j f hj hf C G O w hw
  · intro w hw hm
    exact OneLineCoordinate.maximal_coordinate K D L (by omega) j f hj hf C G O Q
      hblocks hsource w hw hm

end Guralnick.CanonicalOneLineEvaluation
