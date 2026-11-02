import Guralnick.CanonicalSchur
import Guralnick.CanonicalLengthFiltration
import Guralnick.ElementaryCoxeterLongest

/-!
# The finite canonical symmetrizer is its standard sum

The finite sum is a spherical eigenvector by the Hecke quadratic relation.
Canonical corner compatibility forces all its surviving canonical indices
to have the prescribed descents. The length filtration then leaves only
the unique longest element, whose coefficient is one.
-/

noncomputable section
namespace Guralnick.ParabolicStandardSum
open Hecke ParabolicWeb CanonicalSchur
open scoped BigOperators Classical
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

/-- Actual standard coordinates of the finite subgroup sum. -/
theorem standard_coordinate (S : Subgroup (AffinePermutation n)) [Fintype S]
    (d : ℤ) (w : AffinePermutation n) :
    K.standard.repr (FiniteSymmetrizerEigen.sum K S d) w =
      if w ∈ S then LaurentPolynomial.T (d-c.system.length w) else 0 := by
  classical
  simp only [FiniteSymmetrizerEigen.sum, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  by_cases hw : w ∈ S
  · rw [if_pos hw]
    rw [Finset.sum_eq_single (⟨w,hw⟩ : S)]
    · simp
    · intro z _ hz
      have hzw : z.val ≠ w := fun h => hz (Subtype.ext h)
      simp [hzw]
    · simp
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro z _
    have hzw : z.val ≠ w := by
      intro h
      exact hw (h ▸ z.property)
    simp [hzw]

/-- The finite sum lies in the actual simultaneous spherical corner. -/
theorem sum_mem_corner (I : Index n) (D : LongestData c I) :
    letI : Finite (subgroup c I) := D.finite
    letI := Fintype.ofFinite (subgroup c I)
    FiniteSymmetrizerEigen.sum K (subgroup c I) (c.system.length D.longest.val) ∈
      corner I I := by
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  constructor
  · intro i hi
    exact FiniteSymmetrizerEigen.left_eigen K _ _ i
      (Subgroup.subset_closure ⟨i,hi,rfl⟩)
  · intro i hi
    exact FiniteSymmetrizerEigen.right_eigen K _ _ i
      (Subgroup.subset_closure ⟨i,hi,rfl⟩)

/-- Length support of the actual standard sum. -/
theorem standard_support (I : Index n) (D : LongestData c I) :
    letI : Finite (subgroup c I) := D.finite
    letI := Fintype.ofFinite (subgroup c I)
    ∀ w, c.system.length D.longest.val < c.system.length w →
      K.standard.repr
        (FiniteSymmetrizerEigen.sum K (subgroup c I) (c.system.length D.longest.val)) w = 0 := by
  intro w hw
  rw [standard_coordinate]
  apply if_neg
  intro hmem
  exact (not_lt_of_ge (D.length_max ⟨w,hmem⟩)) hw

/-- Generic linear-algebra step, separated from the elementary Coxeter
proofs supplying the two descent facts. -/
theorem standard_sum_of_descent_facts (C : Compatibility K)
    (I : Index n) (D : LongestData c I)
    (length_ge : ∀ w : AffinePermutation n,
      (∀ i ∈ I.val, c.system.IsRightDescent w i) →
      c.system.length D.longest.val ≤ c.system.length w)
    (unique : ∀ w : subgroup c I,
      (∀ i ∈ I.val, c.system.IsRightDescent w.val i) → w.val = D.longest.val) :
    letI : Finite (subgroup c I) := D.finite
    letI := Fintype.ofFinite (subgroup c I)
    K.canonical D.longest.val =
      FiniteSymmetrizerEigen.sum K (subgroup c I) (c.system.length D.longest.val) := by
  classical
  letI : Finite (subgroup c I) := D.finite
  letI := Fintype.ofFinite (subgroup c I)
  let x := FiniteSymmetrizerEigen.sum K (subgroup c I) (c.system.length D.longest.val)
  have hstd := standard_support K I D
  have hcorner : x ∈ corner I I := sum_mem_corner K I D
  have hcan : ∀ w, K.canonical.repr x w ≠ 0 → w = D.longest.val := by
    intro w hw
    have hdes := (C.canonical_support I I x hcorner w hw).2
    have hlo := length_ge w hdes
    have hhi : c.system.length w ≤ c.system.length D.longest.val := by
      by_contra h
      exact hw (canonical_support_length_le K x _ hstd w (Nat.lt_of_not_ge h))
    have hlen := Nat.le_antisymm hhi hlo
    have htop := canonical_coordinate_eq_standard_at_length K x _ hstd w hlen
    have hmem : w ∈ subgroup c I := by
      by_contra h
      have hz : K.standard.repr x w = 0 := by
        rw [standard_coordinate,if_neg h]
      exact hw (htop.trans hz)
    exact unique ⟨w,hmem⟩ hdes
  apply K.canonical.repr.injective
  apply Finsupp.ext
  intro w
  by_cases hw : w = D.longest.val
  · subst w
    rw [Basis.repr_self,Finsupp.single_eq_same]
    rw [canonical_coordinate_eq_standard_at_length K x _ hstd _ rfl]
    rw [standard_coordinate,if_pos D.longest.property,sub_self,LaurentPolynomial.T_zero]
  · rw [Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hw)]
    exact (not_ne_iff.mp (fun h => hw (hcan w h))).symm

/-- The finite canonical symmetrizer formula follows from generic Schur
compatibility and the proved affine-window descent bounds. No independent
parabolic formula or longest-element hypothesis is supplied. -/
theorem standard_sum (C : Compatibility K)
    (I : Index n) (D : LongestData c I) :
    letI : Finite (subgroup c I) := D.finite
    letI := Fintype.ofFinite (subgroup c I)
    K.canonical D.longest.val =
      FiniteSymmetrizerEigen.sum K (subgroup c I) (c.system.length D.longest.val) :=
  standard_sum_of_descent_facts K C I D
    (ElementaryCoxeterLongest.length_ge_of_right_descents c I D)
    (ElementaryCoxeterLongest.eq_longest_of_right_descents c I D)

#print axioms standard_sum_of_descent_facts
#print axioms standard_sum
end Guralnick.ParabolicStandardSum
