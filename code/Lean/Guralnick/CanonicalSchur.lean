import Guralnick.ParabolicWeb

/-!
# The genuine spherical corner and maximal canonical indices

The corner is the actual simultaneous left/right Hecke eigenspace, with
trivial eigenvalue `v^-1`. The only new literature input is the general
parabolic canonical-basis compatibility: canonical indices of a corner
vector have all required left and right descents. It applies to arbitrary
finite parabolics and vectors, and contains no six-family support, gallery
count, correction, or row-sum conclusion.
-/

noncomputable section

namespace Guralnick.CanonicalSchur

open Hecke ParabolicWeb

variable {n : ℕ}

/-- The trivial-induced spherical corner inside the actual Hecke algebra. -/
def corner (I J : Index n) : Submodule R (Hecke.Algebra n) where
  carrier := {x | (∀ i ∈ I.val, H i * x = (LaurentPolynomial.T (-1) : R) • x) ∧
    (∀ j ∈ J.val, x * H j = (LaurentPolynomial.T (-1) : R) • x)}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i hi
      rw [mul_add, hx.1 i hi, hy.1 i hi, smul_add]
    · intro j hj
      rw [add_mul, hx.2 j hj, hy.2 j hj, smul_add]
  smul_mem' := by
    intro a x hx
    constructor
    · intro i hi
      rw [mul_smul_comm, hx.1 i hi, smul_comm]
    · intro j hj
      rw [smul_mul_assoc, hx.2 j hj, smul_comm]

/-- Maximality in the finite-parabolic double coset, expressed using actual
Coxeter descents rather than an arbitrary predicate on numerical matrices. -/
def DoubleMaximal (c : WindowCoxeter n) (I J : Index n)
    (w : AffinePermutation n) : Prop :=
  (∀ i ∈ I.val, c.system.IsLeftDescent w i) ∧
  (∀ j ∈ J.val, c.system.IsRightDescent w j)

/-- Generic canonical compatibility of finite-parabolic spherical corners,
as in Cui's Hecke construction of the Schur canonical basis (Lemma 3.1,
Theorem 3.1 and (3.4)–(3.5)). This is an explicit literature hypothesis. -/
structure Compatibility {c : WindowCoxeter n} (K : KLRealization c) : Prop where
  canonical_support : ∀ (I J : Index n) (x : Hecke.Algebra n),
    x ∈ corner I J → ∀ w, K.canonical.repr x w ≠ 0 → DoubleMaximal c I J w

/-- A nonzero scalar can be cancelled from the spherical eigenconditions,
because the presented Hecke algebra has the specified actual basis. -/
theorem corner_of_cleared {c : WindowCoxeter n} (K : KLRealization c)
    {I J : Index n} {d : R} (hd : d ≠ 0) {x : Hecke.Algebra n}
    (hx : d • x ∈ corner I J) : x ∈ corner I J := by
  constructor
  · intro i hi
    apply scalar_cancel K hd
    have h := hx.1 i hi
    rw [mul_smul_comm, smul_comm] at h
    exact h
  · intro j hj
    apply scalar_cancel K hd
    have h := hx.2 j hj
    rw [smul_mul_assoc, smul_comm] at h
    exact h

variable {m : ℕ} {c : WindowCoxeter (2*m+1)}
variable (K : KLRealization c) (D : ∀ I : Index (2*m+1), LongestData c I)
variable (L : Laws K D)

/-- The actual integral six-map composite preserves the spherical source
and lies in the specified output corner. This follows from its proved
cleared numerator identity and the general parabolic eigenlaws. -/
theorem raw_mem_corner :
    Family.raw K D L ∈ corner (Family.output m) (Family.source m) := by
  apply corner_of_cleared K (Family.denominator_ne_zero K D L)
  rw [Family.raw_cleared K D L]
  constructor
  · intro i hi
    calc
      H i * (symmetrizer K D (Family.output m) * symmetrizer K D (Family.middle m) *
          symmetrizer K D (Family.cyclic m) * symmetrizer K D (Family.source m)) =
          (H i * symmetrizer K D (Family.output m)) * symmetrizer K D (Family.middle m) *
            symmetrizer K D (Family.cyclic m) * symmetrizer K D (Family.source m) := by
              simp only [mul_assoc]
      _ = (LaurentPolynomial.T (-1) : R) •
          (symmetrizer K D (Family.output m) * symmetrizer K D (Family.middle m) *
            symmetrizer K D (Family.cyclic m) * symmetrizer K D (Family.source m)) := by
              rw [L.left_eigen _ _ hi]
              simp only [smul_mul_assoc]
  · intro j hj
    calc
      (symmetrizer K D (Family.output m) * symmetrizer K D (Family.middle m) *
          symmetrizer K D (Family.cyclic m) * symmetrizer K D (Family.source m)) * H j =
          (symmetrizer K D (Family.output m) * symmetrizer K D (Family.middle m) *
            symmetrizer K D (Family.cyclic m)) * (symmetrizer K D (Family.source m) * H j) :=
              mul_assoc _ _ _
      _ = (LaurentPolynomial.T (-1) : R) •
          (symmetrizer K D (Family.output m) * symmetrizer K D (Family.middle m) *
            symmetrizer K D (Family.cyclic m) * symmetrizer K D (Family.source m)) := by
              rw [L.right_eigen _ _ hj, mul_smul_comm]

theorem raw_doubleMaximal (C : Compatibility K) (w : AffinePermutation (2*m+1))
    (hw : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    DoubleMaximal c (Family.output m) (Family.source m) w :=
  C.canonical_support _ _ _ (raw_mem_corner K D L) w hw

end Guralnick.CanonicalSchur
