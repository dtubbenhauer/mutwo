import Guralnick.CanonicalCorrection
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

/-!
# Finite canonical expansions and constant multiplicities

The objects here are actual module bases over the Laurent-polynomial ring.
The finite expansion identity is proved from `Basis.repr`, not supplied as
an assumed answer. The abstract positivity hypotheses are exactly what an
application obtains from a canonical basis and a cleared Hecke numerator.

The main result is the mechanism in the manuscript's full-spherical web:
if all relevant standard coefficients have minimum exponent zero and
constant coefficient one, all canonical multiplicities are one. A second
result recovers the type-F multiplicity when all other contributions have
strictly positive degree. Their geometric/counting applications remain
separate obligations.
-/

noncomputable section

namespace Guralnick.CanonicalBasis

open scoped BigOperators
open Positivity CanonicalCorrection

variable {ι V : Type*} [AddCommGroup V] [Module LP V]

/-- Standard coordinates of an actual vector expanded in another actual
basis. The canonical coordinate support is finite even when the basis
indexing set is infinite. -/
theorem coordinate_expansion (standard canonical : Basis ι LP V) (x : V) (i : ι) :
    standard.repr x i =
      ∑ j ∈ (canonical.repr x).support,
        canonical.repr x j * standard.repr (canonical j) i := by
  classical
  have h := congrArg (fun y : V => standard.repr y i) (canonical.linearCombination_repr x)
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] using h.symm

theorem coordinate_expansion_on (standard canonical : Basis ι LP V) (x : V)
    (S : Finset ι) (hS : (canonical.repr x).support ⊆ S) (i : ι) :
    standard.repr x i =
      ∑ j ∈ S, canonical.repr x j * standard.repr (canonical j) i := by
  classical
  rw [coordinate_expansion standard canonical x i]
  apply Finset.sum_subset hS
  intro j hj hnot
  rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]

/-- The diagonal term can be separated from the remaining finite expansion. -/
theorem split_expansion {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → LP)
    (h : ι → ι → LP) (raw : ι → LP) (i : ι)
    (hi : i ∈ S) (hdiag : h i i = 1)
    (hexp : raw i = ∑ j ∈ S, a j * h i j) :
    raw i = a i + ∑ j ∈ S.erase i, a j * h i j := by
  classical
  rw [hexp, ← Finset.add_sum_erase S (fun j => a j * h i j) hi, hdiag, mul_one]

/-- Positivity of the cleared numerator supplies a nonnegative remainder
at every standard coordinate. No positivity of the quotient `a j` is used. -/
theorem cleared_remainder_nonnegative {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (d : LP) (a : ι → LP) (h : ι → ι → LP) (i : ι)
    (ha : ∀ j ∈ S, Nonnegative (d * a j))
    (hh : ∀ j ∈ S, Nonnegative (h i j)) :
    Nonnegative (d * ∑ j ∈ S.erase i, a j * h i j) := by
  classical
  rw [Finset.mul_sum]
  apply nonnegative_sum
  intro j hj
  have hjS := Finset.mem_of_mem_erase hj
  rw [← mul_assoc]
  exact nonnegative_mul (ha j hjS) (hh j hjS)

/-- Cleared positivity transfers vanishing of a standard coordinate to
vanishing of its canonical coordinate. -/
theorem canonical_zero_of_standard_zero {ι : Type*} (S : Finset ι)
    (d : LP) (a : ι → LP) (h : ι → ι → LP) (raw : ι → LP) (i : ι)
    (hi : i ∈ S) (hd : d ≠ 0) (hdiag : h i i = 1)
    (ha : ∀ j ∈ S, Nonnegative (d * a j))
    (hh : ∀ j ∈ S, Nonnegative (h i j))
    (hexp : raw i = ∑ j ∈ S, a j * h i j) (hzero : raw i = 0) :
    a i = 0 := by
  classical
  have hs := split_expansion S a h raw i hi hdiag hexp
  have he : d * raw i = d * a i + d * ∑ j ∈ S.erase i, a j * h i j := by
    rw [hs, mul_add]
  exact cleared_eq_zero_of_standard_zero hd (ha i hi)
    (cleared_remainder_nonnegative S d a h i ha hh) he hzero

/-- For actual module bases, the canonical support is contained in the
standard support whenever the cleared canonical multiplicities and the
transition coefficients are nonnegative. The finite expansion is proved
from the bases, and no support inclusion is assumed. -/
theorem canonical_support_subset_standard (standard canonical : Basis ι LP V)
    (x : V) (d : LP) (hd : d ≠ 0)
    (hdiag : ∀ i, standard.repr (canonical i) i = 1)
    (hpositive : ∀ i j, Nonnegative (standard.repr (canonical j) i))
    (hcleared : ∀ i ∈ (canonical.repr x).support,
      Nonnegative (d * canonical.repr x i)) :
    (canonical.repr x).support ⊆ (standard.repr x).support := by
  classical
  intro i hi
  apply Finsupp.mem_support_iff.mpr
  intro hzero
  have hz := canonical_zero_of_standard_zero (canonical.repr x).support d
    (fun i => canonical.repr x i) (fun i j => standard.repr (canonical j) i)
    (fun i => standard.repr x i) i hi hd (hdiag i) hcleared
    (fun j _ => hpositive i j) (coordinate_expansion standard canonical x i) hzero
  exact Finsupp.mem_support_iff.mp hi hz

/-- Constant-term extraction from a finite canonical expansion. All other
terms are excluded by their actual Laurent support, not by a numerical
definition of the multiplicity. -/
theorem diagonal_constant {ι : Type*} (S : Finset ι) (a : ι → LP)
    (h : ι → ι → LP) (raw : ι → LP) (i : ι)
    (hi : i ∈ S) (hdiag : h i i = 1)
    (hexp : raw i = ∑ j ∈ S, a j * h i j)
    (hother : ∀ j ∈ S, j ≠ i → LowerBound (a j * h i j) 1) :
    raw i 0 = a i 0 := by
  classical
  rw [split_expansion S a h raw i hi hdiag hexp, coeff_add]
  have hz : (∑ j ∈ S.erase i, a j * h i j) 0 = 0 := by
    apply lowerBound_sum (S.erase i) (fun j => a j * h i j) (a := 1) _ 0 (by omega)
    intro j hj
    obtain ⟨hne, hjS⟩ := Finset.mem_erase.mp hj
    exact hother j hjS hne
  rw [hz, add_zero]

/-- The type-F constant-term argument. The relevance bound gives a
nonnegative lower support bound, bar fixes its multiplicity, and all
auxiliary contributions have positive minimum degree. -/
theorem multiplicity_one {ι : Type*} (S : Finset ι) (a : ι → LP)
    (h : ι → ι → LP) (raw : ι → LP) (i : ι)
    (hi : i ∈ S) (hdiag : h i i = 1)
    (hexp : raw i = ∑ j ∈ S, a j * h i j)
    (hbar : BarSymmetric (a i)) (hlow : LowerBound (a i) 0)
    (hraw : raw i 0 = 1)
    (hother : ∀ j ∈ S, j ≠ i → LowerBound (a j * h i j) 1) :
    a i = 1 := by
  have hc := constant_of_zero_bar_bound hbar hlow
  have hzero := diagonal_constant S a h raw i hi hdiag hexp hother
  rw [hraw] at hzero
  rw [hc, ← hzero, map_one]

/-- Full-spherical multiplicities are one. This proves the entire
constant-multiplicity mechanism from finite basis expansion, cleared
positivity, and the raw standard-coordinate bounds. It does not assume
the canonical coefficients are constant or that they equal one. -/
theorem all_multiplicities_one {ι : Type*} (S : Finset ι)
    (d : LP) (a : ι → LP) (h : ι → ι → LP) (raw : ι → LP)
    (hd : d ≠ 0)
    (hdiag : ∀ i ∈ S, h i i = 1)
    (hpositive : ∀ i ∈ S, ∀ j ∈ S, Nonnegative (h i j))
    (hstrict : ∀ i ∈ S, ∀ j ∈ S, j ≠ i → LowerBound (h i j) 1)
    (hbar : ∀ i ∈ S, BarSymmetric (a i))
    (hcleared : ∀ i ∈ S, Nonnegative (d * a i))
    (hexp : ∀ i ∈ S, raw i = ∑ j ∈ S, a j * h i j)
    (hlow : ∀ i ∈ S, LowerBound (raw i) 0)
    (hconstant : ∀ i ∈ S, raw i 0 = 1) :
    ∀ i ∈ S, a i = 1 := by
  classical
  have halow : ∀ i ∈ S, LowerBound (a i) 0 := by
    intro i hi
    have hs := split_expansion S a h raw i hi (hdiag i hi) (hexp i hi)
    have he : d * raw i = d * a i + d * ∑ j ∈ S.erase i, a j * h i j := by
      rw [hs, mul_add]
    exact cleared_lowerBound hd (hcleared i hi)
      (cleared_remainder_nonnegative S d a h i hcleared (hpositive i hi)) he (hlow i hi)
  intro i hi
  apply multiplicity_one S a h raw i hi (hdiag i hi) (hexp i hi)
    (hbar i hi) (halow i hi) (hconstant i hi)
  intro j hj hne
  simpa only [zero_add] using lowerBound_mul (halow j hj) (hstrict i hi j hj hne)

/-- A version for actual standard and canonical bases. Its expansion
hypothesis is discharged by linear algebra. `S` is the actual support
of the vector's canonical coordinates. -/
theorem basis_multiplicities_one (standard canonical : Basis ι LP V)
    (x : V) (d : LP) (hd : d ≠ 0)
    (hdiag : ∀ i ∈ (canonical.repr x).support, standard.repr (canonical i) i = 1)
    (hpositive : ∀ i ∈ (canonical.repr x).support, ∀ j ∈ (canonical.repr x).support,
      Nonnegative (standard.repr (canonical j) i))
    (hstrict : ∀ i ∈ (canonical.repr x).support, ∀ j ∈ (canonical.repr x).support,
      j ≠ i → LowerBound (standard.repr (canonical j) i) 1)
    (hbar : ∀ i ∈ (canonical.repr x).support, BarSymmetric (canonical.repr x i))
    (hcleared : ∀ i ∈ (canonical.repr x).support, Nonnegative (d * canonical.repr x i))
    (hlow : ∀ i ∈ (canonical.repr x).support, LowerBound (standard.repr x i) 0)
    (hconstant : ∀ i ∈ (canonical.repr x).support, standard.repr x i 0 = 1) :
    ∀ i ∈ (canonical.repr x).support, canonical.repr x i = 1 := by
  apply all_multiplicities_one (canonical.repr x).support d
    (fun i => canonical.repr x i) (fun i j => standard.repr (canonical j) i)
    (fun i => standard.repr x i) hd hdiag hpositive hstrict hbar hcleared
    _ hlow hconstant
  intro i _
  exact coordinate_expansion standard canonical x i

/-- The full-spherical argument for actual bases, including every standard
support index. It does not assume that these indices occur canonically:
support inclusion is first derived from positivity, and constant terms then
force every one of their canonical coefficients to equal one. -/
theorem basis_one_on_standard_support (standard canonical : Basis ι LP V)
    (x : V) (d : LP) (hd : d ≠ 0)
    (hdiag : ∀ i, standard.repr (canonical i) i = 1)
    (hpositive : ∀ i j, Nonnegative (standard.repr (canonical j) i))
    (hstrict : ∀ i j, j ≠ i → LowerBound (standard.repr (canonical j) i) 1)
    (hbar : ∀ i, BarSymmetric (canonical.repr x i))
    (hcleared : ∀ i, Nonnegative (d * canonical.repr x i))
    (hlow : ∀ i ∈ (standard.repr x).support, LowerBound (standard.repr x i) 0)
    (hconstant : ∀ i ∈ (standard.repr x).support, standard.repr x i 0 = 1) :
    ∀ i ∈ (standard.repr x).support, canonical.repr x i = 1 := by
  have hS := canonical_support_subset_standard standard canonical x d hd
    hdiag hpositive (fun i _ => hcleared i)
  apply all_multiplicities_one (standard.repr x).support d
    (fun i => canonical.repr x i) (fun i j => standard.repr (canonical j) i)
    (fun i => standard.repr x i) hd (fun i _ => hdiag i)
    (fun i _ j _ => hpositive i j) (fun i _ j _ hne => hstrict i j hne)
    (fun i _ => hbar i) (fun i _ => hcleared i)
    (fun i _ => coordinate_expansion_on standard canonical x _ hS i) hlow hconstant

/-- The one-line canonicality mechanism for actual bases. The distinguished
standard coordinate is exactly one, every other standard coordinate has
strictly positive support, and the vector is bar fixed in canonical
coordinates. Cleared numerator positivity then proves that the vector is
the distinguished canonical basis element. No maximal-support or canonical
identity is assumed as an additional input. -/
theorem canonical_single_of_positive_proper (standard canonical : Basis ι LP V)
    (x : V) (d : LP) (t : ι) (hd : d ≠ 0)
    (hdiag : ∀ i, standard.repr (canonical i) i = 1)
    (hpositive : ∀ i j, Nonnegative (standard.repr (canonical j) i))
    (hbar : ∀ i, BarSymmetric (canonical.repr x i))
    (hcleared : ∀ i, Nonnegative (d * canonical.repr x i))
    (hleading : standard.repr x t = 1)
    (hproper : ∀ i, i ≠ t → LowerBound (standard.repr x i) 1) :
    x = canonical t := by
  classical
  let S := (canonical.repr x).support
  have hzero : ∀ i, i ≠ t → canonical.repr x i = 0 := by
    intro i hit
    by_cases hi : i ∈ S
    · have hs := split_expansion S (fun i => canonical.repr x i)
        (fun i j => standard.repr (canonical j) i) (fun i => standard.repr x i)
        i hi (hdiag i) (coordinate_expansion standard canonical x i)
      dsimp only at hs
      have he : d * standard.repr x i = d * canonical.repr x i +
          d * ∑ j ∈ S.erase i, canonical.repr x j * standard.repr (canonical j) i := by
        rw [hs, mul_add]
      exact cleared_eq_zero_of_positive_bound hd (hcleared i)
        (cleared_remainder_nonnegative S d (fun i => canonical.repr x i)
          (fun i j => standard.repr (canonical j) i) i
          (fun j _ => hcleared j) (fun j _ => hpositive i j))
        he (hproper i hit) (hbar i) (by omega)
    · exact Finsupp.notMem_support_iff.mp hi
  have ht : canonical.repr x t = 1 := by
    have hS : (canonical.repr x).support ⊆ insert t S := Finset.subset_insert _ _
    have he := coordinate_expansion_on standard canonical x (insert t S) hS t
    rw [Finset.sum_eq_single t] at he
    · rw [hdiag, mul_one, hleading] at he
      exact he.symm
    · intro j _ hjt
      rw [hzero j hjt, zero_mul]
    · simp
  apply canonical.repr.injective
  apply Finsupp.ext
  intro i
  by_cases hit : i = t
  · subst i
    simpa using ht
  · rw [hzero i hit, canonical.repr_self_apply]
    simp [Ne.symm hit]

/-- The same uniqueness proof only needs degree tests at indices that can
occur canonically. This permits the ordinary Hecke realization of a Schur
corner, where counts are naturally indexed by maximal double-coset elements. -/
theorem canonical_single_of_positive_canonical_support (standard canonical : Basis ι LP V)
    (x : V) (d : LP) (t : ι) (hd : d ≠ 0)
    (hdiag : ∀ i, standard.repr (canonical i) i = 1)
    (hpositive : ∀ i j, Nonnegative (standard.repr (canonical j) i))
    (hbar : ∀ i, BarSymmetric (canonical.repr x i))
    (hcleared : ∀ i, Nonnegative (d * canonical.repr x i))
    (hleading : standard.repr x t = 1)
    (hproper : ∀ i ∈ (canonical.repr x).support, i ≠ t →
      LowerBound (standard.repr x i) 1) :
    x = canonical t := by
  classical
  let S := (canonical.repr x).support
  have hzero : ∀ i, i ≠ t → canonical.repr x i = 0 := by
    intro i hit
    by_cases hi : i ∈ S
    · have hs := split_expansion S (fun i => canonical.repr x i)
        (fun i j => standard.repr (canonical j) i) (fun i => standard.repr x i)
        i hi (hdiag i) (coordinate_expansion standard canonical x i)
      dsimp only at hs
      have he : d * standard.repr x i = d * canonical.repr x i +
          d * ∑ j ∈ S.erase i, canonical.repr x j * standard.repr (canonical j) i := by
        rw [hs, mul_add]
      exact cleared_eq_zero_of_positive_bound hd (hcleared i)
        (cleared_remainder_nonnegative S d (fun i => canonical.repr x i)
          (fun i j => standard.repr (canonical j) i) i
          (fun j _ => hcleared j) (fun j _ => hpositive i j))
        he (hproper i hi hit) (hbar i) (by omega)
    · exact Finsupp.notMem_support_iff.mp hi
  have ht : canonical.repr x t = 1 := by
    have hS : (canonical.repr x).support ⊆ insert t S := Finset.subset_insert _ _
    have he := coordinate_expansion_on standard canonical x (insert t S) hS t
    rw [Finset.sum_eq_single t] at he
    · rw [hdiag, mul_one, hleading] at he
      exact he.symm
    · intro j _ hjt
      rw [hzero j hjt, zero_mul]
    · simp
  apply canonical.repr.injective
  apply Finsupp.ext
  intro i
  by_cases hit : i = t
  · subst i
    simpa using ht
  · rw [hzero i hit, canonical.repr_self_apply]
    simp [Ne.symm hit]

end Guralnick.CanonicalBasis
