import Guralnick.CanonicalSpherical
import Guralnick.CanonicalChains
import Guralnick.CanonicalAuxiliary
import Guralnick.FiniteBlocks

/-! # The full-spherical canonical expansion inside the actual Hecke algebra -/

noncomputable section
namespace Guralnick.CanonicalSphericalExpansion
open scoped BigOperators
open Hecke ParabolicWeb CanonicalChains Positivity CanonicalSchur

variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
  (D : ∀ I : Index n, LongestData c I) (L : Laws K D)

theorem meet_self (I : Index n) : meet I I=I := by
  apply Subtype.ext
  exact Finset.inter_self I.val

/-- A split/merge across an unchanged parabolic boundary is the identity. -/
theorem step_self (I : Index n) (x : SphericalMaps.spherical (symmetrizer K D I)) :
    step K D L I I x = x := by
  apply Subtype.ext
  apply Hecke.scalar_cancel K (L.scalar_ne_zero I)
  have h := step_cleared K D L I I x
  rw [meet_self] at h
  rw [h]
  obtain ⟨a,ha⟩ := x.property
  rw [← ha,← mul_assoc,L.absorption I I (Finset.Subset.refl _),smul_mul_assoc]

/-- The rank-zero spherical word is exactly the finite symmetrizer. -/
theorem spherical_zero (hn : 0<n) :
    spherical K D L hn ⟨0,hn⟩ = symmetrizer K D (CanonicalChains.source hn) := by
  unfold spherical twoResult
  change (step K D L (CanonicalChains.source hn) (CanonicalChains.source hn)
    (step K D L (CanonicalChains.source hn) (CanonicalChains.source hn) _)).val = _
  rw [step_self,step_self]
  simp

variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
  (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)
  (P : PositivityInput K) (C : Compatibility K)

def raw (s : ℕ) (hs : s≤m) : Hecke.Algebra (2*m+1) :=
  spherical K D L (by omega) ⟨s,by omega⟩

include P C in
/-- The Gaussian standard coefficients and support classification force
multiplicity one for every full-spherical canonical summand. Both remaining
premises are original coordinate statements, never literature axioms. -/
theorem raw_sum (s : ℕ) (hs : s≤m)
    (hclass : ∀ w, DoubleMaximal c (CanonicalChains.source (by omega))
      (CanonicalChains.source (by omega)) w → K.standard.repr (raw K D L s hs) w ≠ 0 →
      ∃ r, r≤s ∧ w=CanonicalSpherical.index m r)
    (hcoord : ∀ r, r≤s → K.standard.repr (raw K D L s hs) (CanonicalSpherical.index m r) =
      CanonicalAuxiliary.sphericalCoefficient (2*m+1-2*r) (s-r)) :
    raw K D L s hs = ∑ r ∈ Finset.range (s+1), K.canonical (CanonicalSpherical.index m r) := by
  classical
  let R := Finset.range (s+1)
  let S := R.image (CanonicalSpherical.index m)
  have hgauss (r : ℕ) (hr : r≤s) := CanonicalAuxiliary.spherical_standard
    (2*m+1-2*r) (s-r) (by omega)
  have hcoords : ∀ w, DoubleMaximal c (CanonicalChains.source (by omega))
      (CanonicalChains.source (by omega)) w → K.standard.repr (raw K D L s hs) w ≠ 0 →
      LowerBound (K.standard.repr (raw K D L s hs) w) 0 ∧
      (K.standard.repr (raw K D L s hs) w) 0=1 := by
    intro w hm hw
    obtain ⟨r,hr,rfl⟩ := hclass w hm hw
    rw [hcoord r hr]
    exact hgauss r hr
  have hsupport := CanonicalBasis.canonical_support_subset_standard K.standard K.canonical
    (raw K D L s hs)
    (twoDenominator D (CanonicalChains.source (by omega)) (omitNode ⟨s,by omega⟩)
      (CanonicalChains.source (by omega)))
    (two_denominator_ne_zero K D L _ _ _) K.canonical_diagonal P.standard_nonnegative
    (fun w _ => two_cleared_nonnegative K D L P _ _ _ w)
  have hmul (r : ℕ) (hr : r≤s) :
      K.canonical.repr (raw K D L s hs) (CanonicalSpherical.index m r)=1 := by
    apply two_multiplicity_one_of_coordinates K D L P C _ _ _ hcoords
    · simpa only [← FiniteBlocks.Family.source_eq_standard] using
        CanonicalSpherical.index_doubleMaximal (hr.trans hs) c
    · intro hz
      change K.standard.repr (raw K D L s hs) (CanonicalSpherical.index m r)=0 at hz
      rw [hcoord r hr] at hz
      have he := congrArg (fun p : LP => p 0) hz
      dsimp only at he
      rw [(hgauss r hr).2] at he
      change (1 : ℤ)=0 at he
      omega
  have houtside (w : AffinePermutation (2*m+1)) (hw : w∉S) :
      K.canonical.repr (raw K D L s hs) w=0 := by
    by_contra hz
    have hwmax := C.canonical_support _ _ (raw K D L s hs)
      (two_mem_corner K D L _ _ _) w hz
    have hwstandard := Finsupp.mem_support_iff.mp (hsupport (Finsupp.mem_support_iff.mpr hz))
    obtain ⟨r,hr,rfl⟩ := hclass w hwmax hwstandard
    exact hw (Finset.mem_image.mpr ⟨r,Finset.mem_range.mpr (by omega),rfl⟩)
  have hsum : (∑ r ∈ R, K.canonical (CanonicalSpherical.index m r)) =
      ∑ w ∈ S, K.canonical w := by
    rw [Finset.sum_image]
    intro r hr t ht he
    exact CanonicalSpherical.index_injective
      (by have := Finset.mem_range.mp hr; omega)
      (by have := Finset.mem_range.mp ht; omega) he
  change raw K D L s hs = ∑ r ∈ R, K.canonical (CanonicalSpherical.index m r)
  rw [hsum]
  apply K.canonical.repr.injective
  ext w
  simp only [map_sum,Finsupp.finset_sum_apply,K.canonical.repr_self_apply]
  by_cases hw : w∈S
  · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hw
    rw [← he,hmul r (by have := Finset.mem_range.mp hr; omega)]
    simp [he,hw]
  · rw [houtside w hw]
    simp [hw]

/-- Consecutive spherical raw sums differ by the actual canonical element.
No coefficient is defined to equal a desired Gaussian expression. -/
theorem canonical_eq_difference (s : ℕ) (hs : s+1≤m)
    (hprev : raw K D L s (by omega) =
      ∑ r ∈ Finset.range (s+1), K.canonical (CanonicalSpherical.index m r))
    (hnext : raw K D L (s+1) hs =
      ∑ r ∈ Finset.range (s+2), K.canonical (CanonicalSpherical.index m r)) :
    K.canonical (CanonicalSpherical.index m (s+1)) =
      raw K D L (s+1) hs - raw K D L s (by omega) := by
  rw [hnext,hprev,show s+2=(s+1)+1 by omega,Finset.sum_range_succ]
  abel

end Guralnick.CanonicalSphericalExpansion
