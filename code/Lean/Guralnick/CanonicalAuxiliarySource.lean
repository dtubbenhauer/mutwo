import Guralnick.CanonicalOneLineFlags
import Guralnick.MainSourceCoordinate

/-! # Fixed-trivial-source coefficients of the actual auxiliary webs -/

noncomputable section
namespace Guralnick.CanonicalAuxiliarySource
open LaurentLattice LatticeGallery LatticeFlags CanonicalChains CanonicalFlagAuxiliary
  CanonicalOneLineFlags

variable {k : Type} [Field k] {n : ℕ}

theorem lower_self (B : Lattice k n) (h : EndpointBounds B B) :
    finiteLower B B h = ⊥ := by
  change quotientImage B.space (expand (shift k n) B.space) _
    (B.space ⊔ B.space) (lowerEndpoint B B h).property.1
      (lowerEndpoint B B h).property.2 = ⊥
  rw [quotientImage_eq_map,sup_idem]
  exact Submodule.mkQ_map_self _

theorem upper_self (B : Lattice k n) (h : EndpointBounds B B) :
    finiteUpper B B h = ⊤ := by
  change quotientImage B.space (expand (shift k n) B.space) _
    (expand (shift k n) B.space ⊓ expand (shift k n) B.space)
      (upperEndpoint B B h).property.1 (upperEndpoint B B h).property.2 = ⊤
  rw [quotientImage_eq_map]
  simp [Submodule.map_top]

variable (hn : 1<n) (j f : Fin n) (hj : 1≤j.val) (hf : 1≤f.val)
  (source : Flag k n (retained (CanonicalOneLineFlags.src hn)))
  (target : Flag k n (retained (CanonicalOneLineFlags.out hn f)))

theorem finiteF_dimension (T : Theory k n) :
    Module.finrank k (finiteF (targetBase hn f target) (targetF hn f target)
      (targetBase_le_F hn f target) (targetF_le_period hn f target)) = f.val := by
  have h := quotient_dimension T (targetBase hn f target) (targetF hn f target)
    (targetBase_le_F hn f target) (targetF_le_period hn f target)
  have hB : degree k n (targetBase hn f target)=0 := target.degree_eq _
  have hF : degree k n (targetF hn f target)=f.val := target.degree_eq _
  rw [hB,hF,sub_zero] at h
  exact_mod_cast h

include hj hf in
/-- The retained-line source count is proved from the actual flag word.
Equality of its degree-zero endpoint lattices is the fixed-source condition. -/
theorem one_line_source_count [Finite k] (T : Theory k n)
    [FiniteDimensional k (quotientSpace (targetBase hn f target))]
    [Finite (quotientSpace (targetBase hn f target))]
    (hcount : GalleryCounting.FiniteFlagCounts k (quotientSpace (targetBase hn f target)))
    (heq : singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source = targetBase hn f target) :
    (Nat.card (FlagConvolution.Gallery k (oneLineChain (Nat.zero_lt_of_lt hn) j f)
      source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ)
        (CanonicalGallery.qInt f.val * CanonicalGallery.qGauss ((n : ℤ)-1) ((j.val : ℤ)-1)) := by
  have h : EndpointBounds (singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source)
      (targetBase hn f target) :=
    ⟨by simpa only [heq] using stable k n (targetBase hn f target),
     by simpa only [heq] using stable k n (targetBase hn f target)⟩
  rw [Nat.card_congr (oneLineFiniteGalleryEquiv hn j f hj hf source target T h)]
  simp only [heq,lower_self,upper_self]
  exact GalleryCounting.one_line_source_count hcount
    (T.period_dimension (targetBase hn f target)) (finiteF_dimension hn f target T)

variable {source target}

include hj hf in
theorem prime_square_one_line_source_count (G : GeneralLatticeFlagInput)
    (p : ℕ) (hp : p.Prime) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (source : Flag (GaloisField p 2) n (retained (CanonicalOneLineFlags.src hn)))
      (target : Flag (GaloisField p 2) n (retained (CanonicalOneLineFlags.out hn f))),
      AffineLatticePosition.RelativePosition (GaloisField p 2) n target source
        (AffinePermutation.longest n) →
      (Nat.card (FlagConvolution.Gallery (GaloisField p 2)
        (oneLineChain (Nat.zero_lt_of_lt hn) j f) source target) : ℚ) =
        Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2)
          (CanonicalGallery.qInt f.val * CanonicalGallery.qGauss ((n : ℤ)-1) ((j.val : ℤ)-1)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero n := ⟨by omega⟩
  intro source target hpos
  let T := G.lattice_theory (GaloisField p 2) n
  let B := targetBase hn f target
  letI := T.period_finite B
  letI : Finite (quotientSpace B) := Module.finite_of_finite (GaloisField p 2)
  have heq : singleNode ⟨0,Nat.zero_lt_of_lt hn⟩ source = targetBase hn f target := by
    exact (AffineLatticePosition.relativePosition_longest_zero_nodes_eq
      (GaloisField p 2) n hpos ((out_mask hn f 0).mpr (Or.inl (Fin.ext rfl)))
      ((retained_omit _ _).mpr (Fin.ext rfl))).symm
  have hc := one_line_source_count hn j f hj hf source target T
    (G.finite_flag_counts (GaloisField p 2) (quotientSpace B)) heq
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  have hcard : Nat.card (GaloisField p 2) = p^2 := GaloisField.card p 2 (by decide)
  rw [hcard] at hq
  have heval := Polynomial.eval₂_at_apply
    (p := CanonicalGallery.qInt f.val * CanonicalGallery.qGauss ((n : ℤ)-1) ((j.val : ℤ)-1))
    (Int.castRingHom ℚ) ((p^2 : ℕ) : ℤ)
  simp only [Int.coe_castRingHom, Int.cast_natCast, Nat.cast_pow] at heval hq
  exact hq.trans heval.symm

/-- The actual integral one-line Hecke web has the source polynomial
[f]G(N−1,j−1), with its actual chain-weight normalization. -/
theorem one_line_source_coordinate {c : Hecke.WindowCoxeter n}
    (K : Hecke.KLRealization c)
    (D : ∀ I : ParabolicWeb.Index n, ParabolicWeb.LongestData c I)
    (L : ParabolicWeb.Laws K D) (C : FlagConvolution.Input K D L)
    (G : GeneralLatticeFlagInput) (hj : 1≤j.val) (hf : 1≤f.val) :
    K.standard.repr (oneLine K D L (Nat.zero_lt_of_lt hn) j f)
      (AffinePermutation.longest n) =
      normalize (Chain.weight D (oneLineChain (Nat.zero_lt_of_lt hn) j f) -
        c.system.length (AffinePermutation.longest n))
        (CanonicalGallery.qInt f.val * CanonicalGallery.qGauss ((n : ℤ)-1) ((j.val : ℤ)-1)) := by
  rw [oneLine_eq_chain]
  exact FlagConvolution.coordinate_of_uniform_count K D L C _ _ _
    (prime_square_one_line_source_count hn j f hj hf G)

/-- The spherical source polynomial is an actual Grassmannian count. -/
theorem spherical_source_count [Finite k] (hn : 0<n) (s : Fin n) (hs : 0<s.val)
    (source target : Flag k n (retained (CanonicalChains.source hn))) (T : Theory k n)
    [FiniteDimensional k (quotientSpace (targetLattice hn target))]
    [Finite (quotientSpace (targetLattice hn target))]
    (hcount : GalleryCounting.FiniteFlagCounts k (quotientSpace (targetLattice hn target)))
    (heq : sourceLattice hn source = targetLattice hn target) :
    (Nat.card (FlagConvolution.Gallery k (sphericalChain hn s) source target) : ℤ) =
      Polynomial.eval (Nat.card k : ℤ) (CanonicalGallery.qGauss n s.val) := by
  have h : EndpointBounds (sourceLattice hn source) (targetLattice hn target) :=
    ⟨by simpa only [heq] using stable k n (targetLattice hn target),
     by simpa only [heq] using stable k n (targetLattice hn target)⟩
  rw [Nat.card_congr (sphericalFiniteGalleryEquiv T hn s hs source target h)]
  simp only [heq,lower_self,upper_self]
  have hc := GalleryCounting.spherical_count hcount (I₀ := ⊥) (K₀ := ⊤)
    (N := n) (r := 0) (s := s.val) bot_le (by simp)
    (by simpa using T.period_dimension (targetLattice hn target))
  simpa only [Nat.cast_zero,mul_zero,sub_zero] using hc

theorem prime_square_spherical_source_count (hn : 0<n) (s : Fin n) (hs : 0<s.val)
    (G : GeneralLatticeFlagInput) (p : ℕ) (hp : p.Prime) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (source target : Flag (GaloisField p 2) n (retained (CanonicalChains.source hn))),
      AffineLatticePosition.RelativePosition (GaloisField p 2) n target source
        (AffinePermutation.longest n) →
      (Nat.card (FlagConvolution.Gallery (GaloisField p 2)
        (sphericalChain hn s) source target) : ℚ) =
        Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2) (CanonicalGallery.qGauss n s.val) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero n := ⟨by omega⟩
  intro source target hpos
  let T := G.lattice_theory (GaloisField p 2) n
  let B := targetLattice hn target
  letI := T.period_finite B
  letI : Finite (quotientSpace B) := Module.finite_of_finite (GaloisField p 2)
  have heq : sourceLattice hn source = targetLattice hn target := by
    exact (AffineLatticePosition.relativePosition_longest_zero_nodes_eq
      (GaloisField p 2) n hpos ((retained_omit _ _).mpr (Fin.ext rfl))
      ((retained_omit _ _).mpr (Fin.ext rfl))).symm
  have hc := spherical_source_count hn s hs source target T
    (G.finite_flag_counts (GaloisField p 2) (quotientSpace B)) heq
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  have hcard : Nat.card (GaloisField p 2) = p^2 := GaloisField.card p 2 (by decide)
  rw [hcard] at hq
  have heval := Polynomial.eval₂_at_apply (p := CanonicalGallery.qGauss n s.val)
    (Int.castRingHom ℚ) ((p^2 : ℕ) : ℤ)
  simp only [Int.coe_castRingHom, Int.cast_natCast, Nat.cast_pow] at heval hq
  exact hq.trans heval.symm

theorem spherical_source_coordinate {c : Hecke.WindowCoxeter n}
    (K : Hecke.KLRealization c)
    (D : ∀ I : ParabolicWeb.Index n, ParabolicWeb.LongestData c I)
    (L : ParabolicWeb.Laws K D) (C : FlagConvolution.Input K D L)
    (G : GeneralLatticeFlagInput) (hn : 0<n) (s : Fin n) (hs : 0<s.val) :
    K.standard.repr (spherical K D L hn s) (AffinePermutation.longest n) =
      normalize (Chain.weight D (sphericalChain hn s) -
        c.system.length (AffinePermutation.longest n)) (CanonicalGallery.qGauss n s.val) := by
  rw [spherical_eq_chain]
  exact FlagConvolution.coordinate_of_uniform_count K D L C _ _ _
    (prime_square_spherical_source_count hn s hs G)

end Guralnick.CanonicalAuxiliarySource
