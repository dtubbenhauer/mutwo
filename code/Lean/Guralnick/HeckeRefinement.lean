import Guralnick.Hecke
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Data.Finset.Max

/-!
# Actual finite double-coset sums and output refinement

The normalized standard vector is an explicit sum of ordinary standard
Hecke basis elements over a finite double coset. Refinement is proved by
partitioning that actual finite set into double cosets for the smaller
output subgroup. No formula for a manuscript-specific coefficient is
assumed.
-/

noncomputable section

namespace Guralnick.HeckeRefinement

open scoped BigOperators
open Classical Hecke

section DoubleCosets
variable {G : Type*} [Group G]

/-- A finite double coset, defined using multiplication in the actual group. -/
def doubleCoset (P Q : Subgroup G) [Finite P] [Finite Q] (w : G) : Finset G :=
  letI : Fintype P := Fintype.ofFinite _
  letI : Fintype Q := Fintype.ofFinite _
  Finset.univ.image (fun pq : P × Q => (pq.1 : G) * w * pq.2)

theorem mem_doubleCoset (P Q : Subgroup G) [Finite P] [Finite Q] (w x : G) :
    x ∈ doubleCoset P Q w ↔ ∃ p ∈ P, ∃ q ∈ Q, x = p*w*q := by
  simp only [doubleCoset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨p,q⟩, h⟩
    exact ⟨p, p.property, q, q.property, h.symm⟩
  · rintro ⟨p,hp,q,hq,h⟩
    exact ⟨(⟨p,hp⟩,⟨q,hq⟩), h.symm⟩

theorem mem_doubleCoset_iff_class (P Q : Subgroup G) [Finite P] [Finite Q] (w x : G) :
    x ∈ doubleCoset P Q w ↔ Doset.mk P Q w = Doset.mk P Q x := by
  rw [mem_doubleCoset, Doset.eq]

theorem self_mem_doubleCoset (P Q : Subgroup G) [Finite P] [Finite Q] (w : G) :
    w ∈ doubleCoset P Q w := (mem_doubleCoset_iff_class P Q w w).mpr rfl

theorem doubleCoset_nonempty (P Q : Subgroup G) [Finite P] [Finite Q] (w : G) :
    (doubleCoset P Q w).Nonempty := ⟨w, self_mem_doubleCoset P Q w⟩

theorem doubleCoset_subset (P T Q : Subgroup G) [Finite P] [Finite T] [Finite Q]
    (hPT : P ≤ T) {w y : G} (hy : y ∈ doubleCoset T Q w) :
    doubleCoset P Q y ⊆ doubleCoset T Q w := by
  intro x hx
  obtain ⟨p,hp,q,hq,rfl⟩ := (mem_doubleCoset P Q y x).mp hx
  obtain ⟨t,ht,u,hu,rfl⟩ := (mem_doubleCoset T Q w y).mp hy
  apply (mem_doubleCoset T Q w _).mpr
  exact ⟨p*t, T.mul_mem (hPT hp) ht, u*q, Q.mul_mem hu hq, by simp [mul_assoc]⟩

/-- Fine double-coset labels that occur in one coarse double coset. -/
def refinementLabels (P T Q : Subgroup G) [Finite T] [Finite Q] (w : G) :
    Finset (Doset.Quotient (P : Set G) (Q : Set G)) :=
  (doubleCoset T Q w).image (Doset.mk P Q)

/-- The fibre of an actual fine double-coset label is its whole double coset. -/
theorem refinement_fibre (P T Q : Subgroup G) [Finite P] [Finite T] [Finite Q]
    (hPT : P ≤ T) (w : G) (d : Doset.Quotient (P : Set G) (Q : Set G))
    (hd : d ∈ refinementLabels P T Q w) :
    (doubleCoset T Q w).filter (fun x => Doset.mk P Q x = d) = doubleCoset P Q d.out := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hd
  ext x
  rw [Finset.mem_filter, mem_doubleCoset_iff_class P Q _ x, Doset.out_eq']
  constructor
  · rintro ⟨_,hx⟩
    exact hx.symm
  · intro hx
    refine ⟨?_,hx.symm⟩
    apply doubleCoset_subset P T Q hPT hy
    exact (mem_doubleCoset_iff_class P Q y x).mpr hx

end DoubleCosets

variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

/-- Normalized ordinary-standard sum over a finite set of affine elements.
For a double coset, `L` is its maximal Coxeter length. -/
def standardSum (D : Finset (AffinePermutation n)) (L : ℤ) : Hecke.Algebra n :=
  ∑ w ∈ D, (LaurentPolynomial.T (L - c.system.length w) : R) • K.standard w

/-- Its coordinates in the actual ordinary Hecke standard basis. -/
theorem standardSum_coordinate (D : Finset (AffinePermutation n)) (L : ℤ)
    (y : AffinePermutation n) :
    K.standard.repr (standardSum K D L) y =
      if y ∈ D then LaurentPolynomial.T (L-c.system.length y) else 0 := by
  simp [standardSum, map_sum, Basis.repr_self, Finsupp.single_apply, Finset.sum_ite_eq',
    smul_eq_mul]

/-- The normalization ratio is forced by multiplying the Laurent monomials. -/
theorem standardSum_shift (D : Finset (AffinePermutation n)) (L E : ℤ) :
    (LaurentPolynomial.T (L-E) : R) • standardSum K D E = standardSum K D L := by
  simp only [standardSum, Finset.smul_sum, smul_smul, ← LaurentPolynomial.T_add]
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  omega

/-- An actual finite partition gives the normalized refinement identity. -/
theorem standardSum_partition {ι : Type*} (D : Finset (AffinePermutation n))
    (labels : AffinePermutation n → ι) (L : ℤ) (fineLength : ι → ℤ) :
    standardSum K D L =
      ∑ d ∈ D.image labels, (LaurentPolynomial.T (L-fineLength d) : R) •
        standardSum K (D.filter (fun w => labels w = d)) (fineLength d) := by
  have hs : (∑ d ∈ D.image labels, (LaurentPolynomial.T (L-fineLength d) : R) •
      standardSum K (D.filter (fun w => labels w = d)) (fineLength d)) =
      ∑ d ∈ D.image labels, standardSum K (D.filter (fun w => labels w = d)) L := by
    apply Finset.sum_congr rfl
    intro d _
    exact standardSum_shift K _ L (fineLength d)
  rw [hs]
  unfold standardSum
  exact (Finset.sum_fiberwise_of_maps_to (s := D) (t := D.image labels)
    (g := labels) (fun w hw => Finset.mem_image_of_mem labels hw)
    (fun w => (LaurentPolynomial.T (L-c.system.length w) : R) • K.standard w)).symm

/-- Maximal length of a finite double coset, defined from its actual elements. -/
def doubleCosetLength (P Q : Subgroup (AffinePermutation n)) [Finite P] [Finite Q]
    (w : AffinePermutation n) : ℕ :=
  (doubleCoset P Q w).sup c.system.length

theorem doubleCosetLength_eq (P Q : Subgroup (AffinePermutation n)) [Finite P] [Finite Q]
    (w y : AffinePermutation n) (hy : y ∈ doubleCoset P Q w)
    (hmax : ∀ x ∈ doubleCoset P Q w, c.system.length x ≤ c.system.length y) :
    doubleCosetLength (c := c) P Q w = c.system.length y := by
  apply le_antisymm
  · exact Finset.sup_le hmax
  · exact Finset.le_sup hy

/-- The normalized Schur standard vector in the underlying Hecke algebra. -/
def doubleCosetStandard (P Q : Subgroup (AffinePermutation n)) [Finite P] [Finite Q]
    (w : AffinePermutation n) : Hecke.Algebra n :=
  standardSum K (doubleCoset P Q w) (doubleCosetLength (c := c) P Q w)

theorem doubleCosetStandard_coordinate (P Q : Subgroup (AffinePermutation n))
    [Finite P] [Finite Q] (w y : AffinePermutation n) :
    K.standard.repr (doubleCosetStandard K P Q w) y =
      if y ∈ doubleCoset P Q w then
        LaurentPolynomial.T ((doubleCosetLength (c := c) P Q w : ℤ)-c.system.length y) else 0 :=
  standardSum_coordinate K _ _ _

/-- At any actual longest representative, the normalized coordinate is one. -/
theorem doubleCosetStandard_leading (P Q : Subgroup (AffinePermutation n))
    [Finite P] [Finite Q] (w y : AffinePermutation n)
    (hy : y ∈ doubleCoset P Q w)
    (hmax : ∀ x ∈ doubleCoset P Q w, c.system.length x ≤ c.system.length y) :
    K.standard.repr (doubleCosetStandard K P Q w) y = 1 := by
  rw [doubleCosetStandard_coordinate, if_pos hy, doubleCosetLength_eq P Q w y hy hmax]
  simp

/-- The coordinate at a fine longest representative is exactly the
normalization ratio appearing in output refinement. -/
theorem refinement_coordinate (P T Q : Subgroup (AffinePermutation n))
    [Finite P] [Finite T] [Finite Q] (hPT : P ≤ T) (w z y : AffinePermutation n)
    (hz : z ∈ doubleCoset T Q w) (hy : y ∈ doubleCoset P Q z)
    (hmax : ∀ x ∈ doubleCoset P Q z, c.system.length x ≤ c.system.length y) :
    K.standard.repr (doubleCosetStandard K T Q w) y =
      LaurentPolynomial.T ((doubleCosetLength (c := c) T Q w : ℤ)-
        doubleCosetLength (c := c) P Q z) := by
  rw [doubleCosetStandard_coordinate,
    if_pos (doubleCoset_subset P T Q hPT hz hy), doubleCosetLength_eq P Q z y hy hmax]

/-- Output refinement for actual nested finite subgroups and actual
double-coset sums, with the precise length normalization in the paper. -/
theorem doubleCoset_refinement (P T Q : Subgroup (AffinePermutation n))
    [Finite P] [Finite T] [Finite Q] (hPT : P ≤ T) (w : AffinePermutation n) :
    doubleCosetStandard K T Q w =
      ∑ d ∈ refinementLabels P T Q w,
        (LaurentPolynomial.T ((doubleCosetLength (c := c) T Q w : ℤ) -
          doubleCosetLength (c := c) P Q d.out) : R) • doubleCosetStandard K P Q d.out := by
  rw [doubleCosetStandard, standardSum_partition K _ (Doset.mk P Q) _
    (fun d => (doubleCosetLength (c := c) P Q d.out : ℤ))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [refinement_fibre P T Q hPT w d hd]
  rfl

/-- The actual span of normalized double-coset standard vectors in the
presented Hecke algebra. Identification with the usual Schur Hom corner is
a general Schur-basis theorem, separate from this explicit definition. -/
def SchurCorner (P Q : Subgroup (AffinePermutation n)) [Finite P] [Finite Q] :
    Submodule R (Hecke.Algebra n) :=
  Submodule.span R (Set.range (doubleCosetStandard K P Q))

/-- Within an actual Schur corner, every ordinary-standard coordinate in
one double coset has the forced normalization ratio. This applies in
particular to a canonical element once its corner membership is known. -/
theorem corner_coordinate_ratio (P Q : Subgroup (AffinePermutation n))
    [Finite P] [Finite Q] {x : Hecke.Algebra n} (hx : x ∈ SchurCorner K P Q)
    (y z : AffinePermutation n) (hyz : Doset.mk P Q y = Doset.mk P Q z) :
    K.standard.repr x y =
      (LaurentPolynomial.T ((c.system.length z : ℤ)-c.system.length y) : R) *
        K.standard.repr x z := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,rfl⟩ := hx
    rw [doubleCosetStandard_coordinate, doubleCosetStandard_coordinate]
    have hmem : y ∈ doubleCoset P Q w ↔ z ∈ doubleCoset P Q w := by
      rw [mem_doubleCoset_iff_class, mem_doubleCoset_iff_class, hyz]
    by_cases hz : z ∈ doubleCoset P Q w
    · rw [if_pos hz, if_pos (hmem.mpr hz), ← LaurentPolynomial.T_add]
      congr 1
      omega
    · rw [if_neg hz, if_neg (fun h => hz (hmem.mp h)), mul_zero]
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ h₁ h₂ =>
    simpa only [map_add, Finsupp.add_apply, mul_add] using congrArg₂ (·+·) h₁ h₂
  | smul a x hx h =>
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [h]
    ring

end Guralnick.HeckeRefinement
