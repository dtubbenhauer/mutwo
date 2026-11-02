import Guralnick.FiniteSymmetrizerAbsorption

/-! # Left absorption for the raw finite weighted standard sum

This is the left-hand generator argument, before identifying any raw
weighted sum with a canonical symmetrizer. Subgroup membership is reduced
to products of the given simple generators; descents use the quadratic
relation, so no reduced parabolic factorization is assumed.
-/
noncomputable section
namespace Guralnick.FiniteSymmetrizerEigen
open Hecke HeckeInversion
open scoped BigOperators
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

theorem left_standard_step (x : Hecke.Algebra n) (i : Fin n)
    (hx : H i*x=(LaurentPolynomial.T (-1) : R) • x)
    (w : AffinePermutation n)
    (hw : K.standard w*x=(LaurentPolynomial.T (-(c.system.length w : ℤ)) : R) • x) :
    K.standard (w*c.system.simple i)*x=
      (LaurentPolynomial.T (-(c.system.length (w*c.system.simple i) : ℤ)) : R) • x := by
  rcases c.system.length_mul_simple w i with h|h
  · rw [←right_ascent K w i h,mul_assoc,hx,mul_smul_comm,hw,smul_smul,
      ←LaurentPolynomial.T_add,h,Nat.cast_add,Nat.cast_one]
    congr 2
    ring
  · have he := congrArg (fun y : Hecke.Algebra n => y*x) (right_descent K w i h)
    dsimp only at he
    rw [add_mul,smul_mul_assoc,mul_assoc,hx,mul_smul_comm,hw,smul_smul,smul_smul] at he
    have hlen : -(c.system.length (w*c.system.simple i) : ℤ)=1-(c.system.length w : ℤ) := by omega
    have hp : (LaurentPolynomial.T (-(c.system.length (w*c.system.simple i) : ℤ)) : R) • x +
        (((LaurentPolynomial.T (-1) : R)-LaurentPolynomial.T 1)*
          LaurentPolynomial.T (-(c.system.length w : ℤ))) • x =
        ((LaurentPolynomial.T (-1) : R)*LaurentPolynomial.T (-(c.system.length w : ℤ))) • x := by
      rw [←add_smul,hlen,show 1-(c.system.length w : ℤ)=1+(-(c.system.length w : ℤ)) by ring,
        LaurentPolynomial.T_add]
      congr 1
      ring
    apply K.standard.repr.injective
    have hc := congrArg K.standard.repr (he.symm.trans hp.symm)
    simp only [map_add] at hc
    exact add_right_cancel hc

theorem left_standard_of_generators (I : Set (Fin n)) (x : Hecke.Algebra n)
    (hx : ∀ i∈I, H i*x=(LaurentPolynomial.T (-1) : R) • x)
    (w : AffinePermutation n) (hw : w∈Subgroup.closure (c.system.simple '' I)) :
    K.standard w*x=(LaurentPolynomial.T (-(c.system.length w : ℤ)) : R) • x := by
  have hm : w∈Submonoid.closure (c.system.simple '' I) := by
    rw [←generators_monoid (c:=c) I]
    exact hw
  apply Submonoid.closure_induction_right
    (p := fun w _ => K.standard w*x=(LaurentPolynomial.T (-(c.system.length w : ℤ)) : R) • x)
    ?_ ?_ hm
  · simp [standard_one]
  · rintro w _ _ ⟨i,hi,rfl⟩ ih
    exact left_standard_step K x i (hx i hi) w ih

/-- Absorption by the actual finite weighted standard sum, without any
canonical-basis identification as a hypothesis. -/
theorem left_absorption (I : Set (Fin n))
    [Fintype (Subgroup.closure (c.system.simple '' I))]
    (x : Hecke.Algebra n) (hx : ∀ i∈I, H i*x=(LaurentPolynomial.T (-1) : R) • x)
    (d : ℤ) :
    sum K (Subgroup.closure (c.system.simple '' I)) d*x =
      (∑ w : Subgroup.closure (c.system.simple '' I),
        (LaurentPolynomial.T (d-2*c.system.length w.val) : R)) • x := by
  classical
  unfold sum
  rw [Finset.sum_mul,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro w _
  rw [smul_mul_assoc,left_standard_of_generators K I x hx w.val w.property,
    smul_smul,←LaurentPolynomial.T_add]
  congr 2
  ring

#print axioms left_standard_of_generators
#print axioms left_absorption
end Guralnick.FiniteSymmetrizerEigen
