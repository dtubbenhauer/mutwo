import Guralnick.CanonicalOneLineLeading
import Guralnick.CanonicalOneLineEvaluation
import Guralnick.WebLiterature

/-! # Canonicality at the actual one-line packet patterns -/
noncomputable section
namespace Guralnick.CanonicalOneLinePatterns
open Hecke ParabolicWeb CanonicalChains CanonicalSchur WindowPacketMatrix
  CanonicalOneLineLeading CanonicalOneLineEvaluation

variable {m : ℕ}

def rankNode (w : AffinePermutation (2*m+1)) (hw : Supported w) : Fin (2*m+1) :=
  ⟨(packetMatrix m w hw).rank,by have h := (packetMatrix m w hw).rank_le; omega⟩

/-- The strong one-line web is the canonical element of its actual index. -/
theorem strong_canonical (hm : 2 ≤ m) (T : Theory (2*m+1)) (W : WebLiterature T)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : DoubleMaximal T.coxeter (Family.output m) (Family.source m) w)
    (ha : (packetMatrix m w hw).a=1) (hs : (packetMatrix m w hw).s=0)
    (hb : (packetMatrix m w hw).beta=0) :
    oneLine T.kl W.longest W.parabolic (by omega) (rankNode w hw) ⟨m,by omega⟩ =
      T.kl.canonical w := by
  have hr := (packetMatrix m w hw).rank_le
  apply canonical_of_leading hm T.kl W.longest W.parabolic T.positivity W.schur
    W.convolution W.lattice_flags W.coordinates W.matrix_lengths W.block_lengths
    W.finite_longest (rankNode w hw) ⟨m,by omega⟩
    ((packetMatrix m w hw).typeF_rank_positive ha) (by dsimp; omega)
    (by exact hr) (by dsimp [rankNode]; omega) w hw
  · simpa only [← FiniteBlocks.Family.source_eq_standard] using
      PacketCoarsening.strong_doubleMaximal hm T.coxeter W.matrix_lengths w hw hmax hb hs
  · exact strong_leading hm w hw ha hs

/-- The weak one-line web is the canonical element of its actual index. -/
theorem weak_canonical (hm : 2 ≤ m) (T : Theory (2*m+1)) (W : WebLiterature T)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : DoubleMaximal T.coxeter (Family.output m) (Family.source m) w)
    (ha : (packetMatrix m w hw).a=0) (hs : (packetMatrix m w hw).s=0)
    (hb : (packetMatrix m w hw).beta=1) (hd : (packetMatrix m w hw).delta=1) :
    oneLine T.kl W.longest W.parabolic (by omega) (rankNode w hw) ⟨m+1,by omega⟩ =
      T.kl.canonical w := by
  have hr := (packetMatrix m w hw).rank_le
  apply canonical_of_leading hm T.kl W.longest W.parabolic T.positivity W.schur
    W.convolution W.lattice_flags W.coordinates W.matrix_lengths W.block_lengths
    W.finite_longest (rankNode w hw) ⟨m+1,by omega⟩
    (rank_positive_of_weak w hw hb) (by dsimp; omega)
    (by dsimp [rankNode]; omega) (by dsimp [rankNode]; omega) w hw
  · simpa only [← FiniteBlocks.Family.source_eq_standard] using
      PacketCoarsening.weak_doubleMaximal hm T.coxeter W.matrix_lengths w hw hmax hb
  · exact weak_leading hm w hw ha hs hb hd

/-- Reflection identifies the strong-dual canonical element with a concrete
one-line word at the reflected index; its rank remains the original rank. -/
theorem strongDual_canonical (hm : 2 ≤ m) (T : Theory (2*m+1)) (W : WebLiterature T)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : DoubleMaximal T.coxeter (Family.output m) (Family.source m) w)
    (ha : (packetMatrix m w hw).a=0) (hs : (packetMatrix m w hw).s=1)
    (hb : (packetMatrix m w hw).beta=0) (hd : (packetMatrix m w hw).delta=1) :
    oneLine T.kl W.longest W.parabolic (by omega) (rankNode w hw) ⟨m,by omega⟩ =
      T.kl.canonical (AffineReflection.reflect w) := by
  have hp := PacketReflection.parameters_reflect m w hw
  dsimp only at hp
  have h := strong_canonical hm T W (AffineReflection.reflect w)
    (PacketReflection.supported_reflect hw)
    (PacketReflection.doubleMaximal_reflect hm T.coxeter w hmax)
    (by omega) (by omega) (by omega)
  have hr : rankNode (AffineReflection.reflect w) (PacketReflection.supported_reflect hw) =
      rankNode w hw := by
    apply Fin.ext
    exact PacketReflection.rank_reflect m w hw
  rwa [hr] at h

/-- The corresponding concrete canonical word for the weak-dual index. -/
theorem weakDual_canonical (hm : 2 ≤ m) (T : Theory (2*m+1)) (W : WebLiterature T)
    (w : AffinePermutation (2*m+1)) (hw : Supported w)
    (hmax : DoubleMaximal T.coxeter (Family.output m) (Family.source m) w)
    (ha : (packetMatrix m w hw).a=0) (hs : (packetMatrix m w hw).s=1)
    (hb : (packetMatrix m w hw).beta=0) (hd : (packetMatrix m w hw).delta=0) :
    oneLine T.kl W.longest W.parabolic (by omega) (rankNode w hw) ⟨m+1,by omega⟩ =
      T.kl.canonical (AffineReflection.reflect w) := by
  have hp := PacketReflection.parameters_reflect m w hw
  dsimp only at hp
  have h := weak_canonical hm T W (AffineReflection.reflect w)
    (PacketReflection.supported_reflect hw)
    (PacketReflection.doubleMaximal_reflect hm T.coxeter w hmax)
    (by omega) (by omega) (by omega) (by omega)
  have hr : rankNode (AffineReflection.reflect w) (PacketReflection.supported_reflect hw) =
      rankNode w hw := by
    apply Fin.ext
    exact PacketReflection.rank_reflect m w hw
  rwa [hr] at h

end Guralnick.CanonicalOneLinePatterns
