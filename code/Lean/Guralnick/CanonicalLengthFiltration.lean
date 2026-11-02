import Guralnick.FidelityKL

/-!
# Length filtration in the actual Kazhdan–Lusztig basis

Subword triangularity preserves the filtration by Coxeter length. The proof
uses the finite support of a basis expansion; it does not require positivity,
bar invariance, or a further statement about the canonical basis.
-/

noncomputable section

namespace Guralnick.Hecke

open scoped BigOperators

variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

/-- At a maximal length in an actual canonical expansion, the standard and
canonical coefficients agree. Distinct indices at that length cannot occur
in one another's triangular expansion. -/
theorem canonical_coordinate_eq_standard_of_length_max
    (x : Algebra n) (w : AffinePermutation n)
    (hmax : ∀ z ∈ (K.canonical.repr x).support,
      c.system.length z ≤ c.system.length w) :
    K.canonical.repr x w = K.standard.repr x w := by
  classical
  rw [CanonicalBasis.coordinate_expansion K.standard K.canonical x w]
  rw [Finset.sum_eq_single w]
  · rw [K.canonical_diagonal, mul_one]
  · intro z hz hzw
    have hz0 : K.standard.repr (K.canonical z) w = 0 := by
      by_contra hne
      exact hzw (FidelityKL.bruhat_eq_of_length_le
        (K.canonical_support w z hne) (hmax z hz)).symm
    rw [hz0, mul_zero]
  · intro hw
    rw [Finsupp.notMem_support_iff.mp hw, zero_mul]

/-- A bound on standard support bounds canonical support by the same Coxeter
length. A hypothetical coefficient above the bound has a maximal such
coefficient, which survives unchanged in the standard basis. -/
theorem canonical_support_length_le (x : Algebra n) (d : ℕ)
    (hstandard : ∀ w, d < c.system.length w → K.standard.repr x w = 0) :
    ∀ w, d < c.system.length w → K.canonical.repr x w = 0 := by
  classical
  intro w hw
  by_contra hne
  have hwmem : w ∈ (K.canonical.repr x).support := Finsupp.mem_support_iff.mpr hne
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image
    (K.canonical.repr x).support c.system.length ⟨w, hwmem⟩
  have hdz : d < c.system.length z := lt_of_lt_of_le hw (hmax w hwmem)
  have he := canonical_coordinate_eq_standard_of_length_max K x z hmax
  rw [hstandard z hdz] at he
  exact Finsupp.mem_support_iff.mp hz he

/-- At the top permitted length, the two actual basis coordinates coincide. -/
theorem canonical_coordinate_eq_standard_at_length
    (x : Algebra n) (d : ℕ)
    (hstandard : ∀ z, d < c.system.length z → K.standard.repr x z = 0)
    (w : AffinePermutation n) (hw : c.system.length w = d) :
    K.canonical.repr x w = K.standard.repr x w := by
  apply canonical_coordinate_eq_standard_of_length_max K x w
  intro z hz
  rw [hw]
  by_contra h
  exact Finsupp.mem_support_iff.mp hz
    (canonical_support_length_le K x d hstandard z (Nat.lt_of_not_ge h))

/-- The filtration is the same in both bases, including for vectors which
are neither canonical nor bar fixed. -/
theorem standard_support_length_le_iff (x : Algebra n) (d : ℕ) :
    (∀ w, d < c.system.length w → K.standard.repr x w = 0) ↔
      (∀ w, d < c.system.length w → K.canonical.repr x w = 0) := by
  classical
  constructor
  · exact canonical_support_length_le K x d
  · intro hcanonical w hw
    rw [CanonicalBasis.coordinate_expansion K.standard K.canonical x w]
    apply Finset.sum_eq_zero
    intro z hz
    have hzw : c.system.length z < c.system.length w := by
      have hzd : c.system.length z ≤ d := by
        by_contra h
        exact Finsupp.mem_support_iff.mp hz (hcanonical z (Nat.lt_of_not_ge h))
      exact lt_of_le_of_lt hzd hw
    have hz0 : K.standard.repr (K.canonical z) w = 0 := by
      by_contra hne
      have he : w = z := FidelityKL.bruhat_eq_of_length_le
        (K.canonical_support w z hne) (Nat.le_of_lt hzw)
      subst z
      exact Nat.lt_irrefl _ hzw
    rw [hz0, mul_zero]

#print axioms canonical_support_length_le
#print axioms canonical_coordinate_eq_standard_at_length
#print axioms standard_support_length_le_iff

end Guralnick.Hecke
