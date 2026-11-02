import Guralnick.FidelityKL

/-!
# Ordinary KL inversion from the defining basis properties

Reversing reduced Hecke words reindexes the standard basis by group
inversion. This map commutes with bar, so canonical uniqueness proves the
ordinary polynomial inversion identity. No separate invariance input is
used.
-/
noncomputable section
namespace Guralnick.HeckeInversion
open Hecke Positivity CanonicalCorrection
open scoped BigOperators
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

theorem standard_one : K.standard 1 = 1 := by
  simpa [word] using K.standard_reduced [] (by simp [CoxeterSystem.IsReduced])

theorem left_ascent (w : AffinePermutation n) (i : Fin n)
    (h : c.system.length (c.system.simple i*w)=c.system.length w+1) :
    H i*K.standard w=K.standard (c.system.simple i*w) := by
  obtain ⟨l,hl,rfl⟩ := c.system.exists_reduced_word' w
  have hr : c.system.IsReduced (i::l) := by
    change c.system.length (c.system.simple i*c.system.wordProd l)=l.length+1
    exact h.trans (congrArg (·+1) hl)
  rw [K.standard_reduced l hl,←c.system.wordProd_cons,K.standard_reduced _ hr]
  rfl

theorem right_ascent (w : AffinePermutation n) (i : Fin n)
    (h : c.system.length (w*c.system.simple i)=c.system.length w+1) :
    K.standard w*H i=K.standard (w*c.system.simple i) := by
  obtain ⟨l,hl,rfl⟩ := c.system.exists_reduced_word' w
  have hw : c.system.wordProd (l++[i]) = c.system.wordProd l*c.system.simple i := by
    rw [c.system.wordProd_append,c.system.wordProd_cons,c.system.wordProd_nil,mul_one]
  have hr : c.system.IsReduced (l++[i]) := by
    change c.system.length (c.system.wordProd (l++[i]))=(l++[i]).length
    rw [hw,h,hl]
    simp
  rw [K.standard_reduced l hl,←hw,K.standard_reduced _ hr]
  simp [word]

theorem left_descent (w : AffinePermutation n) (i : Fin n)
    (h : c.system.length (c.system.simple i*w)+1=c.system.length w) :
    H i*K.standard w=K.standard (c.system.simple i*w)+
      (LaurentPolynomial.T (-1)-LaurentPolynomial.T 1 : R) • K.standard w := by
  have ha := left_ascent K (c.system.simple i*w) i (by simpa using h.symm)
  rw [c.system.simple_mul_simple_cancel_left] at ha
  rw [←ha,←mul_assoc,quadratic,add_mul,one_mul,mul_assoc]
  rw [←Algebra.smul_def,ha]

theorem right_descent (w : AffinePermutation n) (i : Fin n)
    (h : c.system.length (w*c.system.simple i)+1=c.system.length w) :
    K.standard w*H i=K.standard (w*c.system.simple i)+
      (LaurentPolynomial.T (-1)-LaurentPolynomial.T 1 : R) • K.standard w := by
  have ha := right_ascent K (w*c.system.simple i) i (by simpa using h.symm)
  rw [c.system.simple_mul_simple_cancel_right] at ha
  rw [←ha,mul_assoc,quadratic,mul_add,mul_one]
  rw [←Algebra.smul_def,mul_smul_comm,ha]

theorem finite_expansion (x : Hecke.Algebra n) :
    (∑ w ∈ (K.standard.repr x).support, K.standard.repr x w • K.standard w)=x := by
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using K.standard.linearCombination_repr x

def reverseMap : Hecke.Algebra n →ₗ[R] Hecke.Algebra n :=
  K.standard.constr R (fun w => K.standard w⁻¹)

@[simp] theorem reverseMap_standard (w : AffinePermutation n) :
    reverseMap K (K.standard w)=K.standard w⁻¹ := K.standard.constr_basis _ _ _

@[simp] theorem reverseMap_one : reverseMap K 1=1 := by
  rw [←standard_one K,reverseMap_standard,inv_one,standard_one]

theorem reverseMap_generator_standard (i : Fin n) (w : AffinePermutation n) :
    reverseMap K (H i*K.standard w)=reverseMap K (K.standard w)*H i := by
  have hlen : c.system.length (w⁻¹*c.system.simple i)=c.system.length (c.system.simple i*w) := by
    rw [←c.system.length_inv (c.system.simple i*w)]
    simp
  rcases c.system.length_simple_mul w i with h|h
  · rw [left_ascent K w i h,reverseMap_standard,reverseMap_standard,
      right_ascent K w⁻¹ i (by rw [hlen,c.system.length_inv]; exact h)]
    simp
  · rw [left_descent K w i h,map_add,map_smul,reverseMap_standard,reverseMap_standard,
      right_descent K w⁻¹ i (by rw [hlen,c.system.length_inv]; exact h)]
    simp

theorem reverseMap_generator_mul (i : Fin n) (x : Hecke.Algebra n) :
    reverseMap K (H i*x)=reverseMap K x*H i := by
  classical
  rw [←finite_expansion K x]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,map_sum,map_smul,
    reverseMap_generator_standard]

theorem reverseMap_bar_word (l : List (Fin n)) :
    reverseMap K (K.bar (word l))=K.bar (reverseMap K (word l)) := by
  induction l with
  | nil => simp [word]
  | cons i l ih =>
    change reverseMap K (K.bar (H i*word l))=K.bar (reverseMap K (H i*word l))
    rw [map_mul,K.bar_generator,add_mul,map_add,reverseMap_generator_mul]
    rw [←Algebra.smul_def,map_smul,ih,reverseMap_generator_mul,map_mul,K.bar_generator]
    rw [mul_add,Algebra.smul_def]
    congr 1
    exact Algebra.commutes _ _

theorem reverseMap_bar (x : Hecke.Algebra n) :
    reverseMap K (K.bar x)=K.bar (reverseMap K x) := by
  classical
  have hstd (w : AffinePermutation n) :
      reverseMap K (K.bar (K.standard w))=K.bar (reverseMap K (K.standard w)) := by
    obtain ⟨l,hl,rfl⟩ := c.system.exists_reduced_word' w
    rw [K.standard_reduced l hl]
    exact reverseMap_bar_word K l
  rw [←finite_expansion K x]
  simp only [map_sum,Hecke.bar_smul,map_smul,hstd]

theorem reverseMap_coordinate (x : Hecke.Algebra n) (w : AffinePermutation n) :
    K.standard.repr (reverseMap K x) w⁻¹=K.standard.repr x w := by
  classical
  rw [←finite_expansion K x]
  simp only [map_sum,map_smul,reverseMap_standard,Finsupp.finset_sum_apply,
    Finsupp.smul_apply,smul_eq_mul,K.standard.repr_self_apply,inv_inj]

theorem reverseMap_canonical (w : AffinePermutation n) :
    reverseMap K (K.canonical w)=K.canonical w⁻¹ := by
  apply sub_eq_zero.mp
  apply FidelityKL.bar_fixed_positive_zero K
  · rw [map_sub,←reverseMap_bar,K.bar_canonical,K.bar_canonical]
  · intro y
    have hcoord := reverseMap_coordinate K (K.canonical w) y⁻¹
    simp only [inv_inv] at hcoord
    rw [map_sub,Finsupp.sub_apply,hcoord]
    by_cases hy : y⁻¹=w
    · have hw : y=w⁻¹ := by rw [←hy,inv_inv]
      rw [hy,hw,K.canonical_diagonal,K.canonical_diagonal,sub_self]
      intro a ha
      rfl
    · exact lowerBound_sub (K.canonical_lower y⁻¹ w hy)
        (K.canonical_lower y w⁻¹ (fun h => hy (by rw [h,inv_inv])))

theorem canonical_inversion (y w : AffinePermutation n) :
    K.standard.repr (K.canonical w⁻¹) y⁻¹=K.standard.repr (K.canonical w) y := by
  rw [←reverseMap_canonical,reverseMap_coordinate]

theorem polynomial_inversion (y w : AffinePermutation n) :
    K.polynomial y⁻¹ w⁻¹=K.polynomial y w := by
  apply FidelityKL.normalize_injective ((c.system.length w : ℤ)-c.system.length y)
  have h := canonical_inversion K y w
  simpa only [K.polynomial_normalization,c.system.length_inv] using h

#print axioms polynomial_inversion
end Guralnick.HeckeInversion
