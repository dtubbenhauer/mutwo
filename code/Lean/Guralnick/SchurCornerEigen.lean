import Guralnick.CanonicalRefinement
import Guralnick.FiniteSymmetrizerEigen

/-! # Double-coset standard sums satisfy the spherical eigenconditions -/

noncomputable section
namespace Guralnick.HeckeRefinement
open Hecke HeckeInversion ParabolicWeb CanonicalSchur
open scoped BigOperators
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

theorem standardSum_left_eigen (S : Finset (AffinePermutation n)) (d : ℤ)
    (i : Fin n) (hS : ∀ w ∈ S, c.system.simple i * w ∈ S) :
    H i * standardSum K S d = (LaurentPolynomial.T (-1) : R) • standardSum K S d := by
  classical
  have hr : (∑ w ∈ S, (LaurentPolynomial.T (d-c.system.length w) : R) •
      K.standard (c.system.simple i*w)) =
      ∑ w ∈ S, (LaurentPolynomial.T (d-c.system.length (c.system.simple i*w)) : R) •
        K.standard w := by
    apply Finset.sum_bij (fun w _ => c.system.simple i*w)
    · exact hS
    · intro a ha b hb hab
      exact mul_left_cancel hab
    · intro b hb
      exact ⟨c.system.simple i*b, hS b hb, by simp⟩
    · intro w hw
      rw [c.system.simple_mul_simple_cancel_left]
  unfold standardSum
  simp only [Finset.mul_sum, mul_smul_comm, FiniteSymmetrizerEigen.term_left,
    Finset.sum_add_distrib]
  rw [hr, ←Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [←add_smul, ←mul_smul]
  congr 1
  ring

theorem term_right (d : ℤ) (i : Fin n) (w : AffinePermutation n) :
    (LaurentPolynomial.T (d-c.system.length w) : R) • (K.standard w * H i) =
    (LaurentPolynomial.T (d-c.system.length w) : R) • K.standard (w*c.system.simple i) +
      ((LaurentPolynomial.T (-1) : R) * LaurentPolynomial.T (d-c.system.length w) -
        LaurentPolynomial.T (d-c.system.length (w*c.system.simple i))) • K.standard w := by
  rcases c.system.length_mul_simple w i with h|h
  · rw [right_ascent K w i h,h,Nat.cast_add,Nat.cast_one]
    rw [←LaurentPolynomial.T_add]
    have he : -1+(d-(c.system.length w : ℤ))=d-((c.system.length w : ℤ)+1) := by ring
    rw [he,sub_self,zero_smul,add_zero]
  · rw [right_descent K w i h,smul_add,smul_smul]
    congr 1
    have he : d-(c.system.length (w*c.system.simple i) : ℤ)=
        (d-(c.system.length w : ℤ))+1 := by omega
    rw [he,LaurentPolynomial.T_add,mul_sub]
    congr 1
    ring

theorem standardSum_right_eigen (S : Finset (AffinePermutation n)) (d : ℤ)
    (i : Fin n) (hS : ∀ w ∈ S, w * c.system.simple i ∈ S) :
    standardSum K S d * H i = (LaurentPolynomial.T (-1) : R) • standardSum K S d := by
  classical
  have hr : (∑ w ∈ S, (LaurentPolynomial.T (d-c.system.length w) : R) •
      K.standard (w*c.system.simple i)) =
      ∑ w ∈ S, (LaurentPolynomial.T (d-c.system.length (w*c.system.simple i)) : R) •
        K.standard w := by
    apply Finset.sum_bij (fun w _ => w*c.system.simple i)
    · exact hS
    · intro a ha b hb hab
      exact mul_right_cancel hab
    · intro b hb
      exact ⟨b*c.system.simple i, hS b hb, by simp⟩
    · intro w hw
      rw [c.system.simple_mul_simple_cancel_right]
  unfold standardSum
  simp only [Finset.sum_mul, smul_mul_assoc, term_right, Finset.sum_add_distrib]
  rw [hr, ←Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [←add_smul, ←mul_smul]
  congr 1
  ring

theorem doubleCosetStandard_mem_corner (I J : Index n)
    [Finite (subgroup c I)] [Finite (subgroup c J)] (w : AffinePermutation n) :
    doubleCosetStandard K (subgroup c I) (subgroup c J) w ∈ corner I J := by
  constructor
  · intro i hi
    apply standardSum_left_eigen
    intro z hz
    obtain ⟨p,hp,q,hq,rfl⟩ := (mem_doubleCoset _ _ _ _).mp hz
    apply (mem_doubleCoset _ _ _ _).mpr
    refine ⟨c.system.simple i*p, (subgroup c I).mul_mem
      (Subgroup.subset_closure ⟨i,hi,rfl⟩) hp, q,hq,?_⟩
    simp only [mul_assoc]
  · intro i hi
    apply standardSum_right_eigen
    intro z hz
    obtain ⟨p,hp,q,hq,rfl⟩ := (mem_doubleCoset _ _ _ _).mp hz
    apply (mem_doubleCoset _ _ _ _).mpr
    refine ⟨p,hp,q*c.system.simple i, (subgroup c J).mul_mem hq
      (Subgroup.subset_closure ⟨i,hi,rfl⟩),?_⟩
    simp only [mul_assoc]

theorem schurCorner_le_corner (I J : Index n)
    [Finite (subgroup c I)] [Finite (subgroup c J)] :
    SchurCorner K (subgroup c I) (subgroup c J) ≤ corner I J := by
  apply Submodule.span_le.mpr
  rintro x ⟨w,rfl⟩
  exact doubleCosetStandard_mem_corner K I J w

end Guralnick.HeckeRefinement
