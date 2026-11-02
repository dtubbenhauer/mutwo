import Guralnick.CanonicalApplication
import Guralnick.CanonicalFullCorrection

/-!
# Assembly at actual Hecke coordinates

This file gives the end-to-end algebraic implication for the manuscript's
actual integral six-map element and actual affine permutations. The remaining
coordinate hypotheses are ORIGINAL obligations of the manuscript, not imported
literature. In particular no row sum, canonical multiplicity-one formula, or
full-spherical correction formula is an input.
-/

noncomputable section

namespace Guralnick.CanonicalRowSum

open scoped BigOperators
open Hecke Positivity ParabolicWeb CanonicalCorrection CanonicalFullCorrection

variable {m : ℕ} {c : WindowCoxeter (2*m+1)}
variable (K : KLRealization c) (D : ∀ I : Index (2*m+1), LongestData c I)
variable (L : Laws K D) (P : PositivityInput K)

local instance : DecidableEq (AffinePermutation (2*m+1)) := Classical.decEq _

def familyIndex (hm : 2 ≤ m) (j : Fin m) : AffinePermutation (2*m+1) :=
  Guralnick.Family.upper hm (show 1 ≤ j.val+1 by omega) (by omega)

theorem familyIndex_injective (hm : 2 ≤ m) : Function.Injective (familyIndex hm) := by
  intro j k h
  have haff : Guralnick.Family.affine hm (show 1 ≤ j.val+1 by omega) (by omega) =
      Guralnick.Family.affine hm (show 1 ≤ k.val+1 by omega) (by omega) := by
    apply mul_right_cancel (b := AffinePermutation.longest (2*m+1))
    exact h
  have he := congrArg (fun u => matrixEntry m u 0 (Guralnick.Family.columnShift 2)) haff
  simp only [Guralnick.Family.matrixEntry_eq_prescribedArray] at he
  change j.val = k.val at he
  exact Fin.ext he

/-- Extract a finite named subfamily from a genuine basis expansion. -/
theorem coordinate_readout {ι V : Type*} [AddCommGroup V] [Module LP V]
    (standard canonical : Basis ι LP V) (x : V) (b : ι)
    (e : Fin m → ι) (hinj : Function.Injective e)
    (hfamily : ∀ j, canonical.repr x (e j) = 1)
    (hother : ∀ w, (∀ j, w ≠ e j) →
      LowerBound (canonical.repr x w * standard.repr (canonical w) b) 3) :
    (standard.repr x b) 1 = ∑ j, (standard.repr (canonical (e j)) b) 1 := by
  classical
  let F : Finset ι := Finset.univ.image e
  let S := (canonical.repr x).support ∪ F
  have hexp := CanonicalBasis.coordinate_expansion_on standard canonical x S
    Finset.subset_union_left b
  have heval : (standard.repr x b) 1 =
      ∑ w ∈ S, (canonical.repr x w * standard.repr (canonical w) b) 1 := by
    rw [hexp]
    change coeffHom 1 (∑ w ∈ S, _) = _
    rw [map_sum]
    rfl
  rw [heval]
  have hreduce :
      (∑ w ∈ S, (canonical.repr x w * standard.repr (canonical w) b) 1) =
      ∑ w ∈ F, (canonical.repr x w * standard.repr (canonical w) b) 1 := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro w hw hnot
    apply hother w _ 1 (by omega)
    intro j heq
    apply hnot
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩
  rw [hreduce]
  unfold F
  rw [Finset.sum_image (fun j _ k _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfamily j, one_mul]

/-- Removing a finite named canonical family leaves the actual sum of
all other canonical contributions. This derives the residual degree bound
from individual coordinate tests, rather than assuming a corrected expansion. -/
theorem residual_lowerBound {ι V : Type*} [AddCommGroup V] [Module LP V]
    (standard canonical : Basis ι LP V) (x : V) (b : ι) (n : ℕ) (e : ℕ → ι)
    (hinj : ∀ r < n, ∀ s < n, e r = e s → r=s) (degree : ℤ)
    (hother : ∀ w, (∀ r < n, w ≠ e r) →
      LowerBound (canonical.repr x w * standard.repr (canonical w) b) degree) :
    LowerBound (standard.repr x b - ∑ r ∈ Finset.range n,
      canonical.repr x (e r) * standard.repr (canonical (e r)) b) degree := by
  classical
  let F := (Finset.range n).image e
  let S := (canonical.repr x).support ∪ F
  let f : ι → LP := fun w => canonical.repr x w * standard.repr (canonical w) b
  have hexp : standard.repr x b = ∑ w ∈ S, f w :=
    CanonicalBasis.coordinate_expansion_on standard canonical x S Finset.subset_union_left b
  have hfamily : (∑ w ∈ F, f w) = ∑ r ∈ Finset.range n, f (e r) := by
    apply Finset.sum_image
    intro r hr s hs he
    exact hinj r (Finset.mem_range.mp hr) s (Finset.mem_range.mp hs) he
  have heq : standard.repr x b - ∑ r ∈ Finset.range n, f (e r) =
      ∑ w ∈ S \ F, f w := by
    rw [hexp, ← hfamily, ← Finset.sum_sdiff (Finset.subset_union_right : F ⊆ S)]
    abel
  change LowerBound (standard.repr x b - ∑ r ∈ Finset.range n, f (e r)) degree
  rw [heq]
  apply lowerBound_sum
  intro w hw
  apply hother w
  intro r hr he
  apply (Finset.mem_sdiff.mp hw).2
  exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, he.symm⟩

include P

/-- Multiplicity one for the actual named family. The only remaining local
input is the positive auxiliary contribution at each family standard; all
other-family terms are eliminated by ordinary canonical triangularity. -/
theorem raw_family_multiplicity_one (hm : 2 ≤ m)
    (hcount : ∀ j : Fin m, K.standard.repr (Family.raw K D L) (familyIndex hm j) =
      normalize (CanonicalGallery.gap ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1)
        (CanonicalGallery.count ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1))
    (haux : ∀ (j : Fin m) w, (∀ k : Fin m, w ≠ familyIndex hm k) →
      LowerBound (K.canonical.repr (Family.raw K D L) w *
        K.standard.repr (K.canonical w) (familyIndex hm j)) 1) :
    ∀ j, K.canonical.repr (Family.raw K D L) (familyIndex hm j) = 1 := by
  classical
  have hzeroOne (j : Fin m) := CanonicalApplication.raw_typeF_zero_or_one K D L P
    (familyIndex hm j) (m-(j.val+1)) (hcount j)
  intro j
  let w := familyIndex hm j
  let S := insert w (K.canonical.repr (Family.raw K D L)).support
  have hexp := CanonicalBasis.coordinate_expansion_on K.standard K.canonical
    (Family.raw K D L) S (Finset.subset_insert _ _) w
  have hconst := (CanonicalGallery.typeF_standard (m-(j.val+1))).2
  have hraw : (K.standard.repr (Family.raw K D L) w) 0 = 1 := by
    rw [hcount j]
    exact hconst
  have hother : ∀ z ∈ S, z ≠ w → LowerBound
      (K.canonical.repr (Family.raw K D L) z * K.standard.repr (K.canonical z) w) 1 := by
    intro z hz hzw
    by_cases hf : ∃ k : Fin m, z = familyIndex hm k
    · obtain ⟨k, rfl⟩ := hf
      rcases hzeroOne k with hk | hk
      · rw [hk, zero_mul]
        intro n hn
        rfl
      · rw [hk, one_mul]
        exact K.canonical_lower w (familyIndex hm k) (Ne.symm hzw)
    · exact haux j z (by simpa only [not_exists] using hf)
  have he := CanonicalBasis.diagonal_constant S
    (fun z => K.canonical.repr (Family.raw K D L) z)
    (fun y z => K.standard.repr (K.canonical z) y)
    (fun y => K.standard.repr (Family.raw K D L) y) w
    (Finset.mem_insert_self _ _) (K.canonical_diagonal w) hexp hother
  rcases hzeroOne j with hz | ho
  · dsimp only at he
    rw [hraw] at he
    dsimp only [w] at he
    rw [hz] at he
    change (1 : ℤ) = 0 at he
    omega
  · exact ho

omit P

/-- The corrected element is an actual vector in the presented affine
Hecke algebra. The full-spherical indices are supplied explicitly. -/
def corrected (Z : ℕ → AffinePermutation (2*m+1)) : Hecke.Algebra (2*m+1) :=
  Family.raw K D L - ∑ r ∈ Finset.range (m-1),
    correction (m-r) • K.canonical (Z r)

theorem corrected_standard_coordinate (Z : ℕ → AffinePermutation (2*m+1))
    (w : AffinePermutation (2*m+1)) :
    K.standard.repr (corrected K D L Z) w =
      K.standard.repr (Family.raw K D L) w -
      ∑ r ∈ Finset.range (m-1), correction (m-r) *
        K.standard.repr (K.canonical (Z r)) w := by
  classical
  unfold corrected
  rw [_root_.map_sub K.standard.repr (Family.raw K D L)
    (∑ r ∈ Finset.range (m-1), correction (m-r) • K.canonical (Z r))]
  simp only [map_sum, map_smul,
    Finsupp.sub_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem corrected_canonical_coordinate (Z : ℕ → AffinePermutation (2*m+1))
    (w : AffinePermutation (2*m+1)) :
    K.canonical.repr (corrected K D L Z) w =
      K.canonical.repr (Family.raw K D L) w -
      ∑ r ∈ Finset.range (m-1), if Z r = w then correction (m-r) else 0 := by
  classical
  unfold corrected
  rw [_root_.map_sub K.canonical.repr (Family.raw K D L)
    (∑ r ∈ Finset.range (m-1), correction (m-r) • K.canonical (Z r))]
  simp only [map_sum, map_smul, Basis.repr_self,
    Finsupp.sub_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero]

theorem corrected_coordinate_off_spherical (Z : ℕ → AffinePermutation (2*m+1))
    (w : AffinePermutation (2*m+1))
    (hw : ∀ r < m-1, w ≠ Z r) :
    K.canonical.repr (corrected K D L Z) w =
      K.canonical.repr (Family.raw K D L) w := by
  classical
  rw [corrected_canonical_coordinate]
  have hz : (∑ r ∈ Finset.range (m-1),
      if Z r = w then correction (m-r) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    exact if_neg (Ne.symm (hw r (Finset.mem_range.mp hr)))
  rw [hz, sub_zero]

/-- The original positive residual is reduced to explicit raw and
canonical standard coordinates plus the individual nonspherical margins.
The finite basis decomposition and rank reindexing are proved here. -/
theorem full_residual_positive_of_coordinates
    (Z : ℕ → AffinePermutation (2*m+1))
    (hZ : ∀ r < m-1, ∀ s < m-1, Z r = Z s → r=s)
    (hraw : ∀ r < m-1, K.standard.repr (Family.raw K D L) (Z r) = rawCoordinate (m-r))
    (htransition : ∀ r < m-1, ∀ s < m-1,
      K.standard.repr (K.canonical (Z s)) (Z r) =
        if r ≤ s then transition (m-r) (s-r) else 0)
    (hother : ∀ r < m-1, ∀ w, (∀ s < m-1, w ≠ Z s) →
      LowerBound (K.canonical.repr (Family.raw K D L) w *
        K.standard.repr (K.canonical w) (Z r)) 1) :
    ∀ l, 2 ≤ l → l ≤ m → LowerBound
      (residual (fun t => K.canonical.repr (Family.raw K D L) (Z (m-t))) l) 1 := by
  classical
  intro l hl hlm
  let r := m-l
  have hr : r < m-1 := by dsimp [r]; omega
  have hmr : m-r = l := by dsimp [r]; omega
  have hsplit : r+(l-1) = m-1 := by dsimp [r]; omega
  have hb := residual_lowerBound K.standard K.canonical (Family.raw K D L) (Z r)
    (m-1) Z hZ 1 (hother r hr)
  rw [hraw r hr, hmr] at hb
  let f : ℕ → LP := fun s => K.canonical.repr (Family.raw K D L) (Z s) *
      K.standard.repr (K.canonical (Z s)) (Z r)
  have hfirst : (∑ s ∈ Finset.range r, f s) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hsr := Finset.mem_range.mp hs
    dsimp only [f]
    rw [htransition r hr s (by omega), if_neg (by omega), mul_zero]
  have htail : (∑ h ∈ Finset.range (l-1), f (r+h)) =
      ∑ h ∈ Finset.range (l-1),
        K.canonical.repr (Family.raw K D L) (Z (m-(l-h))) * transition l h := by
    apply Finset.sum_congr rfl
    intro h hh
    have hh' := Finset.mem_range.mp hh
    dsimp only [f]
    rw [htransition r hr (r+h) (by omega), if_pos (by omega), hmr]
    have hsub : r+h-r = h := by omega
    have hz : r+h = m-(l-h) := by dsimp [r]; omega
    rw [hsub, hz]
  have hsum : (∑ s ∈ Finset.range (m-1), f s) =
      ∑ h ∈ Finset.range (l-1),
        K.canonical.repr (Family.raw K D L) (Z (m-(l-h))) * transition l h := by
    rw [← hsplit, Finset.sum_range_add, hfirst, zero_add, htail]
  change LowerBound (rawCoordinate l - ∑ s ∈ Finset.range (m-1), f s) 1 at hb
  rw [hsum] at hb
  exact hb

/-- Finite descending correction for the actual canonical coordinates.
The original residual positivity is explicit: it must come from the
spherical coordinate formula and the proved auxiliary degree margins. -/
theorem raw_full_correction (Z : ℕ → AffinePermutation (2*m+1))
    (hactual : ∀ l, 2 ≤ l → l ≤ m → LowerBound
      (residual (fun t => K.canonical.repr (Family.raw K D L) (Z (m-t))) l) 1)
    (r : ℕ) (hr : r < m-1) :
    K.canonical.repr (Family.raw K D L) (Z r) = correction (m-r) := by
  have h := correction_unique_up_to m
    (fun t => K.canonical.repr (Family.raw K D L) (Z (m-t)))
    (fun t _ _ => Family.raw_canonical_bar K D L (Z (m-t))) hactual
    (m-r) (by omega) (by omega)
  have heq : m-(m-r) = r := by omega
  simpa only [heq] using h

theorem corrected_spherical_zero (Z : ℕ → AffinePermutation (2*m+1))
    (hZ : ∀ r < m-1, ∀ s < m-1, Z r = Z s → r=s)
    (hactual : ∀ l, 2 ≤ l → l ≤ m → LowerBound
      (residual (fun t => K.canonical.repr (Family.raw K D L) (Z (m-t))) l) 1)
    (r : ℕ) (hr : r < m-1) :
    K.canonical.repr (corrected K D L Z) (Z r) = 0 := by
  classical
  rw [corrected_canonical_coordinate, raw_full_correction K D L Z hactual r hr]
  have hs : (∑ s ∈ Finset.range (m-1),
      if Z s = Z r then correction (m-s) else 0) = correction (m-r) := by
    rw [Finset.sum_eq_single r]
    · exact if_pos rfl
    · intro s hs hsr
      exact if_neg (fun he => hsr (hZ s (Finset.mem_range.mp hs) r hr he))
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hr))
  rw [hs, sub_self]

/-- At the fixed trivial-source standard, the corrected actual vector is
exactly the Gaussian residual. Only the two explicit standard-coordinate
identities remain as inputs. -/
theorem corrected_source_coordinate (Z : ℕ → AffinePermutation (2*m+1))
    (hraw : K.standard.repr (Family.raw K D L) (AffinePermutation.longest (2*m+1)) =
      rawCoordinate m)
    (htransition : ∀ r < m-1,
      K.standard.repr (K.canonical (Z r)) (AffinePermutation.longest (2*m+1)) =
        transition m r) :
    K.standard.repr (corrected K D L Z) (AffinePermutation.longest (2*m+1)) =
      residual correction m := by
  rw [corrected_standard_coordinate, hraw]
  unfold CanonicalFullCorrection.residual
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [htransition r (Finset.mem_range.mp hr)]

include P

/-- Conditional assembly of the row sum at the required fixed source.
Every assumption after `Z` is an explicit remaining ORIGINAL coordinate,
indexing, or auxiliary-margin obligation. None is attributed to a cited
paper. Multiplicity one and the correction are conclusions of the preceding
proofs, and the Gaussian residual and critical value are unconditional.
-/
theorem row_sum_of_original_coordinate_obligations (hm : 2 ≤ m)
    (Z : ℕ → AffinePermutation (2*m+1))
    (hZ : ∀ r < m-1, ∀ s < m-1, Z r = Z s → r=s)
    (hdisjoint : ∀ j : Fin m, ∀ r < m-1, familyIndex hm j ≠ Z r)
    (hcount : ∀ j : Fin m, K.standard.repr (Family.raw K D L) (familyIndex hm j) =
      normalize (CanonicalGallery.gap ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1)
        (CanonicalGallery.count ((m-(j.val+1) : ℕ) : ℤ) 1 1 0 1))
    (hauxFamily : ∀ (j : Fin m) w, (∀ k : Fin m, w ≠ familyIndex hm k) →
      LowerBound (K.canonical.repr (Family.raw K D L) w *
        K.standard.repr (K.canonical w) (familyIndex hm j)) 1)
    (hactual : ∀ l, 2 ≤ l → l ≤ m → LowerBound
      (residual (fun t => K.canonical.repr (Family.raw K D L) (Z (m-t))) l) 1)
    (hraw : K.standard.repr (Family.raw K D L) (AffinePermutation.longest (2*m+1)) =
      rawCoordinate m)
    (htransition : ∀ r < m-1,
      K.standard.repr (K.canonical (Z r)) (AffinePermutation.longest (2*m+1)) =
        transition m r)
    (hauxSource : ∀ w, (∀ j : Fin m, w ≠ familyIndex hm j) →
      (∀ r < m-1, w ≠ Z r) →
      LowerBound (K.canonical.repr (Family.raw K D L) w *
        K.standard.repr (K.canonical w) (AffinePermutation.longest (2*m+1))) 3)
    (hgap : ∀ j : Fin m,
      (c.system.length (familyIndex hm j) : ℤ) -
        c.system.length (AffinePermutation.longest (2*m+1)) = gapFormula m (j.val+1)) :
    (∑ j : Fin m, familyMu hm (show 1 ≤ j.val+1 by omega) (by omega) K) =
      (Nat.choose (m+1) 2 : ℤ) := by
  classical
  have hfamily := raw_family_multiplicity_one K D L P hm hcount hauxFamily
  have hcorrectedFamily : ∀ j, K.canonical.repr (corrected K D L Z) (familyIndex hm j) = 1 := by
    intro j
    rw [corrected_coordinate_off_spherical K D L Z _ (hdisjoint j), hfamily j]
  have hother : ∀ w, (∀ j, w ≠ familyIndex hm j) →
      LowerBound (K.canonical.repr (corrected K D L Z) w *
        K.standard.repr (K.canonical w) (AffinePermutation.longest (2*m+1))) 3 := by
    intro w hw
    by_cases hfull : ∃ r, r < m-1 ∧ w = Z r
    · obtain ⟨r, hr, rfl⟩ := hfull
      rw [corrected_spherical_zero K D L Z hZ hactual r hr, zero_mul]
      intro n hn
      rfl
    · have hoff : ∀ r < m-1, w ≠ Z r := by
        intro r hr heq
        exact hfull ⟨r, hr, heq⟩
      rw [corrected_coordinate_off_spherical K D L Z w hoff]
      exact hauxSource w hw hoff
  have hread := coordinate_readout K.standard K.canonical (corrected K D L Z)
    (AffinePermutation.longest (2*m+1)) (familyIndex hm) (familyIndex_injective hm)
    hcorrectedFamily hother
  rw [corrected_source_coordinate K D L Z hraw htransition, corrected_critical hm] at hread
  calc
    (∑ j : Fin m, familyMu hm (show 1 ≤ j.val+1 by omega) (by omega) K) =
        ∑ j : Fin m, (K.standard.repr (K.canonical (familyIndex hm j))
          (AffinePermutation.longest (2*m+1))) 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact familyMu_eq_canonical_coefficient hm (by omega) (by omega) K (hgap j)
    _ = (Nat.choose (m+1) 2 : ℤ) := hread.symm

end Guralnick.CanonicalRowSum
