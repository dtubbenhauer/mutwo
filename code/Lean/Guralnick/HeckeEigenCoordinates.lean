import Guralnick.CanonicalSchur
import Guralnick.CanonicalLengthFiltration

/-! # Top canonical support of a genuine Hecke eigenvector

The simple-generator multiplication rule forces every maximal-length
canonical coefficient of a spherical eigenvector to have the prescribed
descents. This uses triangularity and the Hecke relation, not Schur
canonical-support compatibility or positivity.
-/
noncomputable section
namespace Guralnick.HeckeEigenCoordinates
open Hecke HeckeInversion ParabolicWeb CanonicalSchur
open scoped BigOperators Classical
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

theorem left_coordinate_standard (i : Fin n) (w : AffinePermutation n)
    (hw : c.system.length (c.system.simple i*w)=c.system.length w+1)
    (z : AffinePermutation n) :
    K.standard.repr (H i*K.standard z) (c.system.simple i*w) =
      (if z=w then 1 else 0) +
      (LaurentPolynomial.T (-1)-LaurentPolynomial.T 1 : R) *
        (if z=c.system.simple i*w then 1 else 0) := by
  classical
  have hne : w≠c.system.simple i*w := by intro h; rw [←h] at hw; omega
  by_cases hz : z=w
  · subst z
    rw [left_ascent K w i hw]
    simp [hne]
  · by_cases hs : z=c.system.simple i*w
    · subst z
      rw [left_descent K (c.system.simple i*w) i (by simpa using hw.symm)]
      simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
        smul_eq_mul,c.system.simple_mul_simple_cancel_left,K.standard.repr_self_apply,
        if_neg hne,if_neg (Ne.symm hne),if_pos rfl,mul_one,zero_add]
    · have hsw : c.system.simple i*z≠c.system.simple i*w := by
        intro h
        exact hz (mul_left_cancel h)
      rcases c.system.length_simple_mul z i with h|h
      · rw [left_ascent K z i h]
        simp [hz,hs,hsw]
      · rw [left_descent K z i h]
        simp [hz,hs,hsw]

theorem left_coordinate (x : Hecke.Algebra n) (i : Fin n) (w : AffinePermutation n)
    (hw : c.system.length (c.system.simple i*w)=c.system.length w+1) :
    K.standard.repr (H i*x) (c.system.simple i*w) = K.standard.repr x w +
      (LaurentPolynomial.T (-1)-LaurentPolynomial.T 1 : R) *
        K.standard.repr x (c.system.simple i*w) := by
  classical
  conv_lhs => rw [←finite_expansion K x]
  simp only [Finset.mul_sum,mul_smul_comm,map_sum,map_smul,
    Finsupp.finset_sum_apply,Finsupp.smul_apply,smul_eq_mul,left_coordinate_standard K i w hw]
  simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq',Finset.sum_ite_eq']
  simp only [Finsupp.mem_support_iff]
  split_ifs <;> simp_all [mul_comm]

/-- The coefficient at an ascending neighbor determines the lower one. -/
theorem left_eigen_zero (x : Hecke.Algebra n) (i : Fin n) (w : AffinePermutation n)
    (hx : H i*x=(LaurentPolynomial.T (-1) : R) • x)
    (hw : c.system.length (c.system.simple i*w)=c.system.length w+1)
    (hz : K.standard.repr x (c.system.simple i*w)=0) : K.standard.repr x w=0 := by
  have h := congrArg (fun y : Hecke.Algebra n =>
    K.standard.repr y (c.system.simple i*w)) hx
  dsimp only at h
  rw [left_coordinate K x i w hw,map_smul,Finsupp.smul_apply,smul_eq_mul,hz,
    mul_zero,mul_zero,add_zero] at h
  exact h

/-- Right-hand version, transported through the proved word reversal. -/
theorem right_eigen_zero (x : Hecke.Algebra n) (i : Fin n) (w : AffinePermutation n)
    (hx : x*H i=(LaurentPolynomial.T (-1) : R) • x)
    (hw : c.system.length (w*c.system.simple i)=c.system.length w+1)
    (hz : K.standard.repr x (w*c.system.simple i)=0) : K.standard.repr x w=0 := by
  have hx' := congrArg (reverseMap K) hx
  rw [FiniteSymmetrizerEigen.reverseMap_right_generator,map_smul] at hx'
  have hw' : c.system.length (c.system.simple i*w⁻¹)=c.system.length w⁻¹+1 := by
    have he := c.system.length_inv (w*c.system.simple i)
    simp only [mul_inv_rev,c.system.inv_simple] at he
    rw [he,c.system.length_inv]
    exact hw
  have hz' : K.standard.repr (reverseMap K x) (c.system.simple i*w⁻¹)=0 := by
    have he := reverseMap_coordinate K x (w*c.system.simple i)
    simpa only [mul_inv_rev,c.system.inv_simple,hz] using he
  have h := left_eigen_zero K (reverseMap K x) i w⁻¹ hx' hw' hz'
  rwa [reverseMap_coordinate] at h

/-- Every top canonical index of an eigenvector has all required descents. -/
theorem eigen_top_doubleMaximal (x : Hecke.Algebra n) (I J : Index n)
    (hx : x∈corner I J) (w : AffinePermutation n)
    (hw : K.canonical.repr x w≠0)
    (hmax : ∀ z∈(K.canonical.repr x).support,c.system.length z≤c.system.length w) :
    DoubleMaximal c I J w := by
  have he := canonical_coordinate_eq_standard_of_length_max K x w hmax
  have hstd : ∀ z,c.system.length w<c.system.length z → K.standard.repr x z=0 := by
    apply (standard_support_length_le_iff K x (c.system.length w)).mpr
    intro z hz
    by_contra hne
    exact (not_lt_of_ge (hmax z (Finsupp.mem_support_iff.mpr hne))) hz
  constructor
  · intro i hi
    rcases c.system.length_simple_mul w i with h|h
    · exact False.elim (hw (he.trans (left_eigen_zero K x i w (hx.1 i hi) h
        (hstd _ (by omega)))))
    · change c.system.length (c.system.simple i*w)<c.system.length w
      omega
  · intro i hi
    rcases c.system.length_mul_simple w i with h|h
    · exact False.elim (hw (he.trans (right_eigen_zero K x i w (hx.2 i hi) h
        (hstd _ (by omega)))))
    · change c.system.length (w*c.system.simple i)<c.system.length w
      omega

#print axioms left_eigen_zero
#print axioms right_eigen_zero
#print axioms eigen_top_doubleMaximal
end Guralnick.HeckeEigenCoordinates
