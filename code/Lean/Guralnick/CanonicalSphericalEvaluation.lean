import Guralnick.CanonicalSphericalCoordinates

/-! # Spherical standard and canonical coefficients from generic literature -/
noncomputable section
namespace Guralnick.CanonicalSphericalEvaluation
open Hecke ParabolicWeb CanonicalChains CanonicalSchur CanonicalSphericalCoordinates
  CanonicalSphericalSupport CanonicalSphericalExpansion LaurentLattice LatticeFlags

variable {m : ℕ} (hm : 2≤m) {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
  (C : FlagConvolution.Input K D L) (G : GeneralLatticeFlagInput)
  (input : ∀ (k : Type) [Field k], OrbitMatrix.CoordinateDimensionInput k (2*m+1))

include hm C G input in
/-- Every nonzero maximal spherical coordinate has one of the actual Z_r
indices, with r bounded by the intermediate lattice dimension. -/
theorem standard_support (lengths : OrbitMatrix.ThreeColumnLengthInput c)
    (s : ℕ) (hs0 : 0<s) (hs : s≤m) (w : AffinePermutation (2*m+1))
    (hmax : DoubleMaximal c (CanonicalChains.source (by omega))
      (CanonicalChains.source (by omega)) w)
    (hne : K.standard.repr (raw K D L s hs) w≠0) :
    ∃ r, r≤s ∧ w=CanonicalSpherical.index m r := by
  have hne' : K.standard.repr (Chain.raw K D L (sphericalChain (by omega) ⟨s,by omega⟩)) w≠0 := by
    simpa only [raw,spherical_eq_chain] using hne
  obtain ⟨p,hp,hh⟩ := FlagConvolution.nonempty_gallery_of_nonzero K D L C _ w hne'
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨source,target,hpos,⟨g⟩⟩ := hh
  let Q := coordinates hpos
  obtain ⟨hw,hr⟩ := gallery_supported_rank Q (input (GaloisField p 2))
    (G.lattice_theory (GaloisField p 2) (2*m+1)) ⟨s,by omega⟩ hs0 g
  exact ⟨(WindowPacketMatrix.packetMatrix m w hw).rank,hr,
    spherical_classification hm lengths w hw hmax⟩

include G input in
/-- The Gaussian is counted on genuine galleries over every prime-square
field; it is not assumed as a standard-coordinate formula. -/
theorem prime_square_count (s r : ℕ) (hs0 : 0<s) (hs : s≤m) (hr : r≤m)
    (p : ℕ) (hp : p.Prime) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (source target : Boundary (GaloisField p 2) m),
      AffineLatticePosition.RelativePosition (GaloisField p 2) (2*m+1) target source
        (CanonicalSpherical.index m r) →
      (Nat.card (FlagConvolution.Gallery (GaloisField p 2)
        (sphericalChain (by omega) ⟨s,by omega⟩) source target) : ℚ) =
        Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2)
          (CanonicalGallery.qGauss ((2*m+1 : ℕ)-2*(r : ℤ)) ((s : ℤ)-r)) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro source target hpos
  let T := G.lattice_theory (GaloisField p 2) (2*m+1)
  letI := T.period_finite (base target)
  letI : Finite (CanonicalFlagAuxiliary.quotientSpace (base target)) :=
    Module.finite_of_finite (GaloisField p 2)
  have hc := gallery_count (coordinates hpos) (input (GaloisField p 2)) T
    (G.finite_flag_counts (GaloisField p 2) (CanonicalFlagAuxiliary.quotientSpace (base target)))
    ⟨s,by omega⟩ hs0 (index_supported r)
  rw [index_rank r hr] at hc
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  have hcard : Nat.card (GaloisField p 2)=p^2 := GaloisField.card p 2 (by decide)
  rw [hcard] at hq
  have heval := Polynomial.eval₂_at_apply
    (p := CanonicalGallery.qGauss ((2*m+1 : ℕ)-2*(r : ℤ)) ((s : ℤ)-r))
    (Int.castRingHom ℚ) ((p^2 : ℕ) : ℤ)
  simp only [Int.coe_castRingHom,Int.cast_natCast,Nat.cast_pow] at heval hq
  exact hq.trans heval.symm

include hm C G input in
/-- Actual standard coordinates of the raw spherical word, including all
valid lower spherical indices. -/
theorem standard_coordinate
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D)
    (s r : ℕ) (hs0 : 0<s) (hs : s≤m) (hr : r≤s) :
    K.standard.repr (raw K D L s hs) (CanonicalSpherical.index m r) =
      CanonicalAuxiliary.sphericalCoefficient (2*m+1-2*r) (s-r) := by
  have he := FlagConvolution.coordinate_of_uniform_count K D L C
    (sphericalChain (by omega) ⟨s,by omega⟩) (CanonicalSpherical.index m r)
    (CanonicalGallery.qGauss ((2*m+1 : ℕ)-2*(r : ℤ)) ((s : ℤ)-r))
    (prime_square_count hm G input s r hs0 hs (hr.trans hs))
  have hw := FiniteAuxiliaryBlocks.spherical_weight D hblocks (show 0<2*m+1 by omega)
    (⟨s,by omega⟩ : Fin (2*m+1)) hsource
  have hl := CanonicalSpherical.index_length_gap (hr.trans hs) c
  have hdegree : Chain.weight D (sphericalChain (by omega) ⟨s,by omega⟩) -
      c.system.length (CanonicalSpherical.index m r) =
      2*(((s-r)*((2*m+1-2*r)-(s-r)) : ℕ) : ℤ) := by
    simp only [Nat.cast_mul,Nat.cast_sub hr,
      Nat.cast_sub (show 2*r≤2*m+1 by omega),
      Nat.cast_sub (show s-r≤2*m+1-2*r by omega),Nat.cast_add,Nat.cast_one] at *
    push_cast at hw hl ⊢
    nlinarith
  have hpoly : CanonicalGallery.qGauss ((2*m+1 : ℕ)-2*(r : ℤ)) ((s : ℤ)-r) =
      Gaussian.qBinomial (2*m+1-2*r) (s-r) := by
    have hn : ((2*m+1-2*r : ℕ) : ℤ) = ((2*m+1 : ℕ) : ℤ)-2*r := by
      rw [Nat.cast_sub (show 2*r≤2*m+1 by omega)]
      norm_num
    rw [← Nat.cast_sub hr,← hn]
    exact CanonicalGallery.qGauss_nat (by omega)
  rw [hdegree,hpoly] at he
  simpa only [raw,spherical_eq_chain,CanonicalAuxiliary.sphericalCoefficient] using he

include hm C G input in
/-- The complete full-spherical canonical expansion is proved modulo only
the stated generic Hecke, orbit-coordinate and finite-count literature. -/
theorem raw_canonical_sum (P : PositivityInput K) (S : Compatibility K)
    (lengths : OrbitMatrix.ThreeColumnLengthInput c)
    (hblocks : FiniteBlocks.BlockLengthInput D)
    (hsource : FiniteBlocks.StandardFiniteLongestInput D)
    (s : ℕ) (hs : s≤m) :
    raw K D L s hs = ∑ r ∈ Finset.range (s+1), K.canonical (CanonicalSpherical.index m r) := by
  by_cases hs0 : s=0
  · subst s
    simp only [raw,spherical_zero,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      CanonicalSpherical.index_zero,symmetrizer]
    exact congrArg K.canonical (hsource _)
  · apply CanonicalSphericalExpansion.raw_sum K D L P S s hs
    · exact standard_support hm K D L C G input lengths s (by omega) hs
    · exact fun r hr => standard_coordinate hm K D L C G input hblocks hsource s r (by omega) hs hr

end Guralnick.CanonicalSphericalEvaluation
