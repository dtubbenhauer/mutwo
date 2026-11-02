import Guralnick.Hecke

/-!
# Bar involutivity from the canonical basis

The scalar action of bar and its fixed canonical basis already force bar to
square to the identity. No separate involutivity assumption is needed.
-/

noncomputable section
open scoped BigOperators

namespace Guralnick.KLDerivedBar

/-- Expand in the canonical basis, apply bar twice, and invert each Laurent
coefficient twice. Only `bar_scalar` and `bar_canonical` are used as bar laws. -/
theorem bar_involutive {n : ℕ} {c : Hecke.WindowCoxeter n}
    (K : Hecke.KLRealization c) : Function.Involutive K.bar := by
  classical
  have bar_smul (r : Hecke.R) (x : Hecke.Algebra n) :
      K.bar (r • x) = LaurentPolynomial.invert r • K.bar x := by
    rw [Algebra.smul_def, map_mul, K.bar_scalar, Algebra.smul_def]
  have invert_twice (r : Hecke.R) :
      LaurentPolynomial.invert (LaurentPolynomial.invert r) = r :=
    LaurentPolynomial.involutive_invert r
  intro x
  have hx : (∑ w ∈ (K.canonical.repr x).support,
      K.canonical.repr x w • K.canonical w) = x := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      K.canonical.linearCombination_repr x
  calc
    K.bar (K.bar x) = K.bar (K.bar (∑ w ∈ (K.canonical.repr x).support,
        K.canonical.repr x w • K.canonical w)) := congrArg (fun y => K.bar (K.bar y)) hx.symm
    _ = ∑ w ∈ (K.canonical.repr x).support,
        K.canonical.repr x w • K.canonical w := by
      simp only [map_sum, bar_smul, K.bar_canonical, invert_twice]
    _ = x := hx

end Guralnick.KLDerivedBar
