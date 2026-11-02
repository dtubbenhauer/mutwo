import Guralnick.SLCoordinateAlgebra
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Ring.Divisibility.Lemmas

/-!
# The determinant-one equation is reduced

A column Euler derivation sends `det - 1` to `det`. A square divisor of the
former must also divide the latter, hence divides one. Thus `det - 1` is
squarefree and its principal ideal is radical. This proves the missing
reducedness comparison with the usual determinant presentation in every
characteristic.
-/
noncomputable section
open scoped BigOperators
namespace Guralnick.SLCoordinate
open MvPolynomial
variable (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι]

/-- Weight one on one matrix column and zero on all other variables. -/
def columnWeight (j : ι) (ij : ι × ι) : ℕ := if ij.2 = j then 1 else 0

/-- Every determinant monomial uses exactly one entry of the chosen column. -/
theorem determinant_columnHomogeneous (j : ι) :
    (determinantPolynomial k ι).IsWeightedHomogeneous (columnWeight ι j) 1 := by
  rw [determinantPolynomial, Matrix.det_apply]
  apply (weightedHomogeneousSubmodule k (columnWeight ι j) 1).sum_mem
  intro σ hσ
  rw [Units.smul_def]
  apply (weightedHomogeneousSubmodule k (columnWeight ι j) 1).toAddSubgroup.zsmul_mem
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun i : ι => (X (σ i,i) : MvPolynomial (ι × ι) k))
    (fun i : ι => columnWeight ι j (σ i,i))
    (fun i _ => isWeightedHomogeneous_X k (columnWeight ι j) (σ i,i))
  simpa [columnWeight] using h

/-- The Euler operator in one column. -/
def columnEuler (j : ι) (p : MvPolynomial (ι × ι) k) : MvPolynomial (ι × ι) k :=
  ∑ ij : ι × ι, columnWeight ι j ij • (X ij * pderiv ij p)

theorem columnEuler_det_sub_one (j : ι) :
    columnEuler k ι j (determinantPolynomial k ι - 1) = determinantPolynomial k ι := by
  have h := (determinant_columnHomogeneous k ι j).sum_weight_X_mul_pderiv
  simpa [columnEuler] using h

omit [Fintype ι] [DecidableEq ι] in
/-- A repeated factor divides every partial derivative. -/
theorem square_dvd_pderiv (a p : MvPolynomial (ι × ι) k) (ij : ι × ι)
    (h : a*a ∣ p) : a ∣ pderiv ij p := by
  obtain ⟨b, rfl⟩ := h
  refine ⟨2 * pderiv ij a * b + a * pderiv ij b, ?_⟩
  simp only [pderiv_mul]
  ring

/-- The determinant-one polynomial has no repeated factor, in any characteristic. -/
theorem determinant_sub_one_squarefree [Nonempty ι] :
    Squarefree (determinantPolynomial k ι - 1) := by
  intro a ha
  have hd : a ∣ determinantPolynomial k ι := by
    rw [← columnEuler_det_sub_one k ι (Classical.choice ‹Nonempty ι›)]
    apply Finset.dvd_sum
    intro ij hij
    exact dvd_nsmul_of_dvd _ (dvd_mul_of_dvd_right (square_dvd_pderiv k ι a _ ij ha) _)
  have hp : a ∣ determinantPolynomial k ι - 1 := dvd_trans (dvd_mul_right a a) ha
  exact isUnit_of_dvd_one ((dvd_sub hd hp).trans (by simp))

/-- The ordinary determinant-one ideal is radical, including the empty matrix case. -/
theorem determinantIdeal_isRadical : (determinantIdeal k ι).IsRadical := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    simp only [determinantIdeal, determinantPolynomial, Matrix.det_isEmpty, sub_self]
    rw [Ideal.span_singleton_eq_bot.mpr rfl]
    exact Ideal.isRadical_bot
  | inr h =>
    letI := h
    exact isRadical_iff_span_singleton.mp (determinant_sub_one_squarefree k ι).isRadical

/-- Point evaluation has precisely the expected determinant-one kernel. -/
theorem evaluation_ker_eq_determinantIdeal [IsAlgClosed k] :
    RingHom.ker (polynomialEvaluation k ι) = determinantIdeal k ι := by
  rw [evaluation_ker_eq_vanishingIdeal, vanishingIdeal_eq_radical,
    (determinantIdeal_isRadical k ι).radical]

/-- The usual affine-group coordinate algebra, not only its reduction,
is isomorphic to the polynomial-function model used in the formalization. -/
def quotientDeterminantEquiv [IsAlgClosed k] :
    (MvPolynomial (ι × ι) k ⧸ determinantIdeal k ι) ≃ₐ[k] CoordinateAlgebra k ι :=
  (Ideal.quotientEquivAlgOfEq k (evaluation_ker_eq_determinantIdeal k ι).symm).trans
    (Ideal.quotientKerEquivRange (polynomialEvaluation k ι))

@[simp] theorem quotientDeterminantEquiv_mk [IsAlgClosed k]
    (p : MvPolynomial (ι × ι) k) :
    quotientDeterminantEquiv k ι (Ideal.Quotient.mk (determinantIdeal k ι) p) =
      (polynomialEvaluation k ι).rangeRestrict p := by
  rfl

#print axioms determinant_sub_one_squarefree
#print axioms evaluation_ker_eq_determinantIdeal

end Guralnick.SLCoordinate
