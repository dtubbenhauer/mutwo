import Guralnick.ParabolicStandardSum
import Guralnick.HeckeRefinement
import Guralnick.ParabolicCosetFactorization

/-! # Integral inclusion of nested spherical ideals

A finite set stable under left parabolic multiplication is partitioned by
removing a coset of minimum length at each step. Its weighted standard sum
is a monomial multiple of the finite symmetrizer times a standard basis
vector. All operations take place over the integral Laurent ring.
-/
noncomputable section
namespace Guralnick.ParabolicIdealInclusion
open Hecke ParabolicWeb HeckeRefinement
open scoped BigOperators Classical
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

theorem standard_mul_of_length (u x : AffinePermutation n)
    (h : c.system.length (u*x)=c.system.length u+c.system.length x) :
    K.standard u*K.standard x=K.standard (u*x) := by
  obtain ⟨l,hl,rfl⟩ := c.system.exists_reduced_word' u
  obtain ⟨r,hr,rfl⟩ := c.system.exists_reduced_word' x
  have hred : c.system.IsReduced (l++r) := by
    change c.system.length (c.system.wordProd (l++r))=(l++r).length
    rw [c.system.wordProd_append,h,hl,hr,List.length_append]
  rw [K.standard_reduced l hl,K.standard_reduced r hr,
    ←c.system.wordProd_append,K.standard_reduced _ hred]
  simp [word]

def coset (S : Subgroup (AffinePermutation n)) [Fintype S] (x : AffinePermutation n) :
    Finset (AffinePermutation n) := Finset.univ.image (fun u : S => u.val*x)

theorem mem_coset (S : Subgroup (AffinePermutation n)) [Fintype S] (x w : AffinePermutation n) :
    w∈coset S x ↔ ∃ u : S, u.val*x=w := by simp [coset]

theorem self_mem_coset (S : Subgroup (AffinePermutation n)) [Fintype S] (x : AffinePermutation n) :
    x∈coset S x := (mem_coset S x x).mpr ⟨1,by simp⟩

theorem coset_factor (I : Index n) (D : LongestData c I)
    (hstd : letI : Finite (subgroup c I) := D.finite
      letI := Fintype.ofFinite (subgroup c I)
      K.canonical D.longest.val = FiniteSymmetrizerEigen.sum K (subgroup c I)
        (c.system.length D.longest.val))
    (d : ℤ) (x : AffinePermutation n)
    (hadd : ∀ u : subgroup c I,
      c.system.length (u.val*x)=c.system.length u.val+c.system.length x) :
    letI : Finite (subgroup c I) := D.finite
    letI := Fintype.ofFinite (subgroup c I)
    standardSum K (coset (subgroup c I) x) d =
      (LaurentPolynomial.T (d-c.system.length D.longest.val-c.system.length x) : R) •
        (K.canonical D.longest.val*K.standard x) := by
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  unfold standardSum coset
  rw [Finset.sum_image]
  · rw [hstd]
    simp only [FiniteSymmetrizerEigen.sum,Finset.sum_mul,smul_mul_assoc,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [standard_mul_of_length K u.val x (hadd u),smul_smul,
      ←LaurentPolynomial.T_add,hadd u,Nat.cast_add]
    congr 2
    ring
  · intro u _ v _ huv
    apply Subtype.ext
    exact mul_right_cancel huv

theorem stable_sum_mem (I : Index n) (D : LongestData c I)
    (hstd : letI : Finite (subgroup c I) := D.finite
      letI := Fintype.ofFinite (subgroup c I)
      K.canonical D.longest.val = FiniteSymmetrizerEigen.sum K (subgroup c I)
        (c.system.length D.longest.val))
    (hadd : ∀ x : AffinePermutation n,
      (∀ u : subgroup c I, c.system.length x ≤ c.system.length (u.val*x)) →
      ∀ u : subgroup c I, c.system.length (u.val*x)=c.system.length u.val+c.system.length x)
    (d : ℤ) (F : Finset (AffinePermutation n))
    (hstable : ∀ (u : subgroup c I) w, w∈F → u.val*w∈F) :
    standardSum K F d ∈ SphericalMaps.spherical (K.canonical D.longest.val) := by
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  revert hstable
  induction' F using Finset.strongInductionOn with F ih
  intro hstable
  by_cases hF : F.Nonempty
  · obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image F c.system.length hF
    let C := coset (subgroup c I) x
    have hCF : C⊆F := by
      intro w hw
      obtain ⟨u,rfl⟩ := (mem_coset _ x w).mp hw
      exact hstable u x hx
    have hxC : x∈C := self_mem_coset _ x
    have hsmall : F\C ⊂ F := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset,?_⟩
      intro he
      have h := hx
      rw [←he] at h
      exact (Finset.mem_sdiff.mp h).2 hxC
    have hrest : ∀ (u : subgroup c I) w, w∈F\C → u.val*w∈F\C := by
      intro u w hw
      obtain ⟨hwF,hwC⟩ := Finset.mem_sdiff.mp hw
      refine Finset.mem_sdiff.mpr ⟨hstable u w hwF,?_⟩
      intro huC
      obtain ⟨v,hv⟩ := (mem_coset _ x _).mp huC
      apply hwC
      apply (mem_coset _ x w).mpr
      refine ⟨u⁻¹*v,?_⟩
      have h := congrArg (fun z : AffinePermutation n => u.val⁻¹*z) hv
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel_left] using h
    have hrestmem := ih (F\C) hsmall hrest
    have hCmem : standardSum K C d∈SphericalMaps.spherical (K.canonical D.longest.val) := by
      rw [coset_factor K I D hstd d x (hadd x (fun u => hmin _ (hstable u x hx)))]
      apply Submodule.smul_mem
      exact ⟨K.standard x,rfl⟩
    have he : standardSum K C d+standardSum K (F\C) d=standardSum K F d := by
      unfold standardSum
      simpa only [add_comm] using (Finset.sum_sdiff (f := fun w =>
        (LaurentPolynomial.T (d-c.system.length w) : R) • K.standard w) hCF)
    rw [←he]
    exact Submodule.add_mem _ hCmem hrestmem
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simp [standardSum]

theorem subgroup_sum (S : Subgroup (AffinePermutation n)) [Fintype S] (d : ℤ) :
    standardSum K (S : Set (AffinePermutation n)).toFinset d = FiniteSymmetrizerEigen.sum K S d := by
  simp only [standardSum,Set.toFinset,Finset.sum_map,Function.Embedding.subtype_apply,
    FiniteSymmetrizerEigen.sum]
  apply Fintype.sum_equiv (Equiv.refl S)
  intro w
  rfl

theorem inclusion_of_length_add (C : CanonicalSchur.Compatibility K)
    (D : ∀ I : Index n, LongestData c I)
    (hadd : ∀ (I : Index n) (x : AffinePermutation n),
      (∀ u : subgroup c I, c.system.length x ≤ c.system.length (u.val*x)) →
      ∀ u : subgroup c I, c.system.length (u.val*x)=c.system.length u.val+c.system.length x)
    (I J : Index n) (hIJ : I.val⊆J.val) :
    SphericalMaps.spherical (symmetrizer K D J) ≤
      SphericalMaps.spherical (symmetrizer K D I) := by
  letI : Finite (subgroup c J) := (D J).finite
  letI := Fintype.ofFinite (subgroup c J)
  have hsub : subgroup c I ≤ subgroup c J := by
    apply Subgroup.closure_mono
    exact Set.image_mono hIJ
  have hmem : symmetrizer K D J ∈ SphericalMaps.spherical (symmetrizer K D I) := by
    have hs := stable_sum_mem K I (D I) (ParabolicStandardSum.standard_sum K C I (D I))
      (hadd I) (c.system.length (D J).longest.val)
      (subgroup c J : Set (AffinePermutation n)).toFinset
      (fun u w hw => Set.mem_toFinset.mpr ((subgroup c J).mul_mem
        (hsub u.property) (Set.mem_toFinset.mp hw)))
    rw [subgroup_sum,←ParabolicStandardSum.standard_sum K C J (D J)] at hs
    exact hs
  rintro x ⟨y,rfl⟩
  exact SphericalMaps.right_closed _ ⟨_,hmem⟩ y

#print axioms stable_sum_mem
#print axioms inclusion_of_length_add

/-- Integral spherical inclusion is a consequence of the established
Schur corner theorem and elementary actual-window/coset calculations. -/
theorem inclusion (C : CanonicalSchur.Compatibility K)
    (D : ∀ I : Index n, LongestData c I) (I J : Index n) (hIJ : I.val⊆J.val) :
    SphericalMaps.spherical (symmetrizer K D J) ≤
      SphericalMaps.spherical (symmetrizer K D I) :=
  inclusion_of_length_add K C D (ParabolicCosetFactorization.length_mul_of_minimal c) I J hIJ

#print axioms inclusion
end Guralnick.ParabolicIdealInclusion
