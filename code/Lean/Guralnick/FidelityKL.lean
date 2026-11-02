import Guralnick.CanonicalHecke

/-!
# Semantic rigidity of the assumed KL realization

The literature interface cannot choose a different coefficient system on
the fixed Coxeter model: reduced words determine the standard basis, the
specified scalar and generator formulas determine bar, and bar/triangularity
determine the canonical basis. Polynomial normalization is injective.
These are new proofs about the interface, not additional input hypotheses.
They do not prove that all the separate literature interfaces are satisfiable.
-/
noncomputable section
namespace Guralnick.FidelityKL
open Hecke Positivity CanonicalCorrection
open scoped BigOperators

theorem normalize_injective (d : ℤ) : Function.Injective (normalize d) := by
  intro P Q h
  ext a
  have hp:=Finsupp.mapDomain_apply (normalization_exponent_injective d) P.toFinsupp a
  have hq:=Finsupp.mapDomain_apply (normalization_exponent_injective d) Q.toFinsupp a
  have he:=congrArg (fun f : LaurentPolynomial ℤ => f (d-2*(a : ℤ))) h
  exact hp.symm.trans (he.trans hq)

variable {n : ℕ} {c : WindowCoxeter n} (K L : KLRealization c)

theorem standard_eq : K.standard=L.standard := by
  apply DFunLike.ext
  intro w
  obtain ⟨l,hl,rfl⟩:=c.system.exists_reduced_word' w
  rw [K.standard_reduced l hl,L.standard_reduced l hl]

theorem bar_word_eq (l : List (Fin n)) : K.bar (word l)=L.bar (word l) := by
  induction l with
  | nil => simp [word]
  | cons i l ih =>
    change K.bar (H i*word l)=L.bar (H i*word l)
    rw [map_mul,map_mul,K.bar_generator,L.bar_generator,ih]

theorem bar_standard_eq (w : AffinePermutation n) :
    K.bar (K.standard w)=L.bar (K.standard w) := by
  obtain ⟨l,hl,rfl⟩:=c.system.exists_reduced_word' w
  rw [K.standard_reduced l hl]
  exact bar_word_eq K L l

theorem bar_eq (x : Hecke.Algebra n) : K.bar x=L.bar x := by
  classical
  have hx : (∑ w ∈ (K.standard.repr x).support, K.standard.repr x w • K.standard w)=x := by
    simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using K.standard.linearCombination_repr x
  rw [←hx]
  simp only [map_sum,Hecke.bar_smul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [bar_standard_eq K L w]

/-- Subword Bruhat support cannot contain a distinct index of equal or
larger length. This derives the necessary strictness from the definition. -/
theorem bruhat_eq_of_length_le {y w : AffinePermutation n}
    (h : Bruhat c y w) (hle : c.system.length w≤c.system.length y) : y=w := by
  obtain ⟨a,b,hab,hred,ha,hb⟩:=h
  have hla:=c.system.length_wordProd_le a
  have hlb : c.system.length w=b.length := by simpa only [CoxeterSystem.IsReduced,hb] using hred
  rw [ha] at hla
  have he:=hab.eq_of_length_le (by omega)
  rw [←ha,←hb,he]

/-- There is no nonzero bar-fixed vector whose standard coefficients all
have strictly positive degree. Positivity is not assumed in this argument. -/
theorem bar_fixed_positive_zero (x : Hecke.Algebra n) (hbar : K.bar x=x)
    (hpositive : ∀ w, LowerBound (K.standard.repr x w) 1) : x=0 := by
  classical
  by_contra hx
  have hrepr : K.canonical.repr x≠0 := by
    intro h
    apply hx
    apply K.canonical.repr.injective
    simpa only [map_zero] using h
  obtain ⟨w,hw,hmax⟩:=Finset.exists_max_image (K.canonical.repr x).support
    c.system.length (Finsupp.support_nonempty_iff.mpr hrepr)
  have hcoord:=CanonicalBasis.coordinate_expansion K.standard K.canonical x w
  have hs : (∑ z ∈ (K.canonical.repr x).support,
      K.canonical.repr x z * K.standard.repr (K.canonical z) w)=K.canonical.repr x w := by
    rw [Finset.sum_eq_single w]
    · rw [K.canonical_diagonal,mul_one]
    · intro z hz hzw
      have hz0 : K.standard.repr (K.canonical z) w=0 := by
        by_contra hne
        exact hzw (bruhat_eq_of_length_le (K.canonical_support w z hne) (hmax z hz)).symm
      rw [hz0,mul_zero]
    · exact fun h => False.elim (h hw)
  rw [hs] at hcoord
  have hlo : LowerBound (K.canonical.repr x w) 1 := by rw [←hcoord]; exact hpositive w
  exact (Finsupp.mem_support_iff.mp hw)
    (eq_zero_of_positive_bar_bound (Hecke.canonical_coordinate_barSymmetric K hbar w) hlo (by norm_num))

/-- Canonical bases satisfying the interface are unique, with no extra
positivity input and no family-specific coefficient premise. -/
theorem canonical_eq : K.canonical=L.canonical := by
  apply DFunLike.ext
  intro w
  apply sub_eq_zero.mp
  apply bar_fixed_positive_zero K (K.canonical w-L.canonical w)
  · rw [map_sub K.bar (K.canonical w) (L.canonical w),K.bar_canonical,
      bar_eq K L (L.canonical w),L.bar_canonical]
  · intro y
    have hs:=standard_eq K L
    by_cases hy : y=w
    · subst y
      have hd : K.standard.repr (L.canonical w) w=1 := by rw [hs,L.canonical_diagonal]
      rw [map_sub K.standard.repr (K.canonical w) (L.canonical w)]
      simp only [Finsupp.sub_apply,K.canonical_diagonal,hd,sub_self]
      intro a ha
      rfl
    · have hL : LowerBound (K.standard.repr (L.canonical w) y) 1 := by
        rw [hs]
        exact L.canonical_lower y w hy
      rw [map_sub K.standard.repr (K.canonical w) (L.canonical w)]
      exact lowerBound_sub (K.canonical_lower y w hy) hL

theorem polynomial_eq (y w : AffinePermutation n) : K.polynomial y w=L.polynomial y w := by
  apply normalize_injective ((c.system.length w : ℤ)-c.system.length y)
  rw [←K.polynomial_normalization,←L.polynomial_normalization,standard_eq K L,canonical_eq K L]

/-- The numerical family coefficient is consequently independent of
which witness to the general KL basis theorem is supplied. -/
theorem familyMu_eq {m j : ℕ} {c : WindowCoxeter (2*m+1)}
    (K L : KLRealization c) (hm : 2≤m) (hj : 1≤j) (hjm : j≤m) :
    familyMu hm hj hjm K=familyMu hm hj hjm L := by
  unfold familyMu
  rw [polynomial_eq K L]

end Guralnick.FidelityKL
