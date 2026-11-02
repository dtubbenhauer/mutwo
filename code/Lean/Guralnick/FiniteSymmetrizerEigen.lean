import Guralnick.KLInversion

/-!
# The finite symmetrizer eigenvalue from its standard sum

The generator exchanges two elements of the actual finite subgroup. The
Hecke quadratic relation and the two possible Coxeter lengths give its
eigenvalue. No parabolic eigenvalue theorem is assumed.
-/
noncomputable section
namespace Guralnick.FiniteSymmetrizerEigen
open Hecke HeckeInversion
open scoped BigOperators
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

def sum (S : Subgroup (AffinePermutation n)) [Fintype S] (d : ℤ) : Hecke.Algebra n :=
  ∑ w : S, (LaurentPolynomial.T (d-c.system.length w.val) : R) • K.standard w.val

theorem term_left (d : ℤ) (i : Fin n) (w : AffinePermutation n) :
    (LaurentPolynomial.T (d-c.system.length w) : R) • (H i*K.standard w) =
    (LaurentPolynomial.T (d-c.system.length w) : R) • K.standard (c.system.simple i*w) +
      ((LaurentPolynomial.T (-1) : R) * LaurentPolynomial.T (d-c.system.length w) -
        LaurentPolynomial.T (d-c.system.length (c.system.simple i*w))) • K.standard w := by
  rcases c.system.length_simple_mul w i with h|h
  · rw [left_ascent K w i h,h,Nat.cast_add,Nat.cast_one]
    rw [←LaurentPolynomial.T_add]
    have he : -1+(d-(c.system.length w : ℤ))=d-((c.system.length w : ℤ)+1) := by ring
    rw [he,sub_self,zero_smul,add_zero]
  · rw [left_descent K w i h,smul_add,smul_smul]
    congr 1
    have he : d-(c.system.length (c.system.simple i*w) : ℤ)=
        (d-(c.system.length w : ℤ))+1 := by omega
    rw [he,LaurentPolynomial.T_add,mul_sub]
    congr 1
    ring

theorem left_eigen (S : Subgroup (AffinePermutation n)) [Fintype S]
    (d : ℤ) (i : Fin n) (hi : c.system.simple i∈S) :
    H i*sum K S d=(LaurentPolynomial.T (-1) : R) • sum K S d := by
  classical
  let e : S ≃ S := Equiv.mulLeft (⟨c.system.simple i,hi⟩ : S)
  have he (w : S) : (e w).val=c.system.simple i*w.val := rfl
  have hr : (∑ w : S, (LaurentPolynomial.T (d-c.system.length w.val) : R) •
      K.standard (c.system.simple i*w.val)) =
      ∑ w : S, (LaurentPolynomial.T (d-c.system.length (c.system.simple i*w.val)) : R) •
        K.standard w.val := by
    apply Fintype.sum_equiv e
    intro w
    simp only [he,c.system.simple_mul_simple_cancel_left]
  unfold sum
  simp only [Finset.mul_sum,mul_smul_comm,term_left,Finset.sum_add_distrib]
  rw [hr]
  rw [←Finset.sum_add_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [←add_smul,←mul_smul]
  congr 1
  ring

theorem reverseMap_involutive (x : Hecke.Algebra n) : reverseMap K (reverseMap K x)=x := by
  classical
  rw [←finite_expansion K x]
  simp only [map_sum,map_smul,reverseMap_standard,inv_inv]

theorem reverseMap_right_generator (x : Hecke.Algebra n) (i : Fin n) :
    reverseMap K (x*H i)=H i*reverseMap K x := by
  have h := congrArg (reverseMap K) (reverseMap_generator_mul K i (reverseMap K x))
  simpa only [reverseMap_involutive] using h.symm

theorem reverseMap_sum (S : Subgroup (AffinePermutation n)) [Fintype S] (d : ℤ) :
    reverseMap K (sum K S d)=sum K S d := by
  classical
  simp only [sum,map_sum,map_smul,reverseMap_standard]
  apply Fintype.sum_equiv (Equiv.inv S)
  intro w
  change (LaurentPolynomial.T (d-c.system.length w.val) : R) • K.standard w.val⁻¹ =
    LaurentPolynomial.T (d-c.system.length w.val⁻¹) • K.standard w.val⁻¹
  rw [c.system.length_inv]

theorem right_eigen (S : Subgroup (AffinePermutation n)) [Fintype S]
    (d : ℤ) (i : Fin n) (hi : c.system.simple i∈S) :
    sum K S d*H i=(LaurentPolynomial.T (-1) : R) • sum K S d := by
  have h := congrArg (reverseMap K) (left_eigen K S d i hi)
  simpa only [reverseMap_generator_mul,map_smul,reverseMap_sum] using h

#print axioms left_eigen
#print axioms right_eigen
end Guralnick.FiniteSymmetrizerEigen
