import Guralnick.CanonicalSchur
import Guralnick.FiniteSymmetrizerLeftAbsorption

/-!
# The eigen-corner reduction to products of finite standard symmetrizers

The external canonical-support statement concerns literal products in the
parabolic ideals. Clearing a vector's left and right generator eigenvalues
places a nonzero scalar multiple in that product. Nonvanishing is proved
from the actual Poincare sum. Thus no identification of eigenspaces with
parabolic ideals is hidden in the external input.
-/
noncomputable section
namespace Guralnick.CanonicalSchurEigenReduction
open Hecke ParabolicWeb CanonicalSchur
open scoped BigOperators
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I)

/-- The literal weighted finite standard sum, defined before its canonical
interpretation. This definition does not use Schur compatibility. -/
def rawSum (I : Index n) : Hecke.Algebra n :=
  letI : Finite (subgroup c I) := (D I).finite
  letI := Fintype.ofFinite (subgroup c I)
  FiniteSymmetrizerEigen.sum K (subgroup c I) (c.system.length (D I).longest.val)

/-- The source-level canonical basis theorem for the intersection of actual
parabolic ideals, restricted to products already in that intersection.
Williamson §2.3 identifies its canonical basis by maximal double-coset
indices; (2.2.2) gives the literal finite standard sums used here. No
eigen-corner assertion or family-specific vector is assumed. -/
structure ProductCompatibility : Prop where
  canonical_support : ∀ (I J : Index n) (x : Hecke.Algebra n) (w : AffinePermutation n),
    K.canonical.repr (rawSum K D I * x * rawSum K D J) w ≠ 0 →
      DoubleMaximal c I J w

/-- Right absorption is subgroup-generator induction, not a consequence
of a canonical finite-symmetrizer formula. -/
theorem right_absorption (I : Index n) (x : Hecke.Algebra n)
    (hx : ∀ i∈I.val,x*H i=(LaurentPolynomial.T (-1) : R) • x) :
    x*rawSum K D I=scalar D I • x := by
  letI : Finite (subgroup c I) := (D I).finite
  letI := Fintype.ofFinite (subgroup c I)
  letI : Fintype (Subgroup.closure (c.system.simple '' (I.val : Set (Fin n)))) :=
    Fintype.ofFinite (subgroup c I)
  exact FiniteSymmetrizerEigen.absorption K (I.val : Set (Fin n)) x hx
    (c.system.length (D I).longest.val)

/-- The analogous left absorption, again on literal standard sums. -/
theorem left_absorption (I : Index n) (x : Hecke.Algebra n)
    (hx : ∀ i∈I.val,H i*x=(LaurentPolynomial.T (-1) : R) • x) :
    rawSum K D I*x=scalar D I • x := by
  letI : Finite (subgroup c I) := (D I).finite
  letI := Fintype.ofFinite (subgroup c I)
  letI : Fintype (Subgroup.closure (c.system.simple '' (I.val : Set (Fin n)))) :=
    Fintype.ofFinite (subgroup c I)
  exact FiniteSymmetrizerEigen.left_absorption K (I.val : Set (Fin n)) x hx
    (c.system.length (D I).longest.val)

/-- A corner vector becomes an actual parabolic product after multiplying
by the two explicitly defined Poincare scalars. -/
theorem product_cleared (I J : Index n) (x : Hecke.Algebra n)
    (hx : x∈corner I J) :
    rawSum K D I*x*rawSum K D J=(scalar D I*scalar D J) • x := by
  rw [left_absorption K D I x hx.1,smul_mul_assoc,right_absorption K D J x hx.2,
    smul_smul]

/-- Elementary clearing supplies the former eigen-corner support input.
No canonical standard-sum theorem is used in this conversion, avoiding a
circular argument in the subsequent construction of that theorem. -/
def toCompatibility (P : ProductCompatibility K D) : Compatibility K where
  canonical_support I J x hx w hw := by
    apply P.canonical_support I J x w
    rw [product_cleared K D I J x hx,map_smul,Finsupp.smul_apply,smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero (scalar_ne_zero D I) (scalar_ne_zero D J)) hw

#print axioms product_cleared
#print axioms toCompatibility
end Guralnick.CanonicalSchurEigenReduction
