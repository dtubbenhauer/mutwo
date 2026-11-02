import Guralnick.ParabolicCosetFactorization
import Guralnick.WindowExamples

/-!
# The five spherical cosets in the rank-one seed

These certificates describe actual affine permutations. Their increasing
windows prove minimality in the finite right coset. The previously proved
parabolic factorization theorem then gives length additivity for every
finite subgroup element, without an enumeration of the 120 elements.
-/

noncomputable section
namespace Guralnick.SeedCosets
open Hecke ParabolicWeb

/-- Identity, `s₀`, `s₁s₀`, `s₄s₀`, and `s₁s₄s₀`, in that order. -/
def certificate (k : Fin 5) : WindowCertificate 5 where
  residue := ![![0,1,2,3,4], ![4,1,2,3,0], ![4,0,2,3,1],
    ![3,1,2,4,0], ![3,0,2,4,1]] k
  inverse := ![![0,1,2,3,4], ![4,1,2,3,0], ![1,4,2,3,0],
    ![4,1,2,0,3], ![1,4,2,0,3]] k
  winding := if k = 0 then 0 else ![-1,0,0,0,1]

theorem accepted (k : Fin 5) : (certificate k).check = true := by
  fin_cases k <;> decide

def coset (k : Fin 5) : AffinePermutation 5 :=
  (certificate k).toAffine (accepted k)

def degree : Fin 5 → ℕ := ![0,1,2,2,3]

theorem coset_zero : coset 0 = 1 := by
  apply AffinePermutation.ext <;> decide

theorem simple_zero (c : WindowCoxeter 5) : c.system.simple 0 = coset 1 := by
  apply AffineAdjacentInversions.ext_entry
  funext i
  rw [c.simple_window]
  fin_cases i <;> rfl

theorem simple_one_mul (c : WindowCoxeter 5) :
    c.system.simple 1 * coset 1 = coset 2 := by
  rw [c.simple_finite (0 : Fin 5) 1 (by decide)]
  apply AffinePermutation.ext <;> decide

theorem simple_four_mul (c : WindowCoxeter 5) :
    c.system.simple 4 * coset 1 = coset 3 := by
  rw [c.simple_finite (3 : Fin 5) 4 (by decide)]
  apply AffinePermutation.ext <;> decide

theorem simple_one_four_mul (c : WindowCoxeter 5) :
    c.system.simple 1 * coset 3 = coset 4 := by
  rw [c.simple_finite (0 : Fin 5) 1 (by decide)]
  apply AffinePermutation.ext <;> decide

theorem simple_four_one_mul (c : WindowCoxeter 5) :
    c.system.simple 4 * coset 2 = coset 4 := by
  rw [c.simple_finite (3 : Fin 5) 4 (by decide)]
  apply AffinePermutation.ext <;> decide

theorem length_coset (c : WindowCoxeter 5) (k : Fin 5) :
    c.system.length (coset k) = degree k := by
  rw [c.length_formula]
  fin_cases k <;> decide

theorem increasing (k : Fin 5) : StrictMono (coset k).entry := by
  fin_cases k <;> decide

theorem no_finite_descents (c : WindowCoxeter 5) (k : Fin 5)
    (s : Fin 5) (hs : s ∈ (Family.source 2).val) :
    ¬c.system.IsRightDescent (coset k) s := by
  have hs0 : s ≠ 0 := by
    simpa [Family.source, Family.sourceSet] using hs
  obtain ⟨a,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hs0
  rw [c.finite_descent _ a.castSucc a.succ (by simp)]
  exact not_lt_of_gt (increasing k (by simp))

theorem length_mul (c : WindowCoxeter 5) (k : Fin 5)
    (u : subgroup c (Family.source 2)) :
    c.system.length (coset k * u.val) = degree k + c.system.length u.val := by
  rw [ParabolicCosetFactorization.length_mul_right_of_no_descents c
    (Family.source 2) (coset k) (no_finite_descents c k) u, length_coset]

theorem word_zero (c : WindowCoxeter 5) :
    c.system.wordProd [0] = coset 1 := by
  simp only [c.system.wordProd_cons, c.system.wordProd_nil, mul_one, simple_zero]

theorem word_one_zero (c : WindowCoxeter 5) :
    c.system.wordProd [1,0] = coset 2 := by
  rw [c.system.wordProd_cons, word_zero, simple_one_mul]

theorem word_four_zero (c : WindowCoxeter 5) :
    c.system.wordProd [4,0] = coset 3 := by
  rw [c.system.wordProd_cons, word_zero, simple_four_mul]

theorem word_one_four_zero (c : WindowCoxeter 5) :
    c.system.wordProd [1,4,0] = coset 4 := by
  rw [c.system.wordProd_cons, word_four_zero, simple_one_four_mul]

theorem source_eq : Family.source 2 = CanonicalChains.source (by decide : 0 < 5) :=
  FiniteBlocks.Family.source_eq_standard 2

theorem finite_zero_winding (c : WindowCoxeter 5)
    (u : subgroup c (Family.source 2)) : u.val.winding = 0 := by
  obtain ⟨σ,hσ⟩ := ElementaryCoxeterFinite.source_le_finite c
    (by simpa only [source_eq] using u.property)
  rw [← hσ]
  rfl

theorem coset_mul_ne_longest (c : WindowCoxeter 5) (k : Fin 5) (hk : k ≠ 0)
    (u : subgroup c (Family.source 2)) :
    coset k * u.val ≠ AffinePermutation.longest 5 := by
  intro h
  have hw := congrArg (fun w : AffinePermutation 5 =>
    w.winding (u.val.residue.symm 0)) h
  dsimp only at hw
  rw [AffinePermutation.mul_winding, finite_zero_winding c u,
    AffinePermutation.longest_winding] at hw
  simp only [Pi.zero_apply, zero_add, Equiv.apply_symm_apply] at hw
  fin_cases k <;> first | exact hk rfl | norm_num [coset, certificate,
    WindowCertificate.toAffine] at hw

theorem affine_top : coset 4 = Guralnick.Family.affine
    (by decide : 2 ≤ 2) (by decide : 1 ≤ 1) (by decide : 1 ≤ 2) := by
  apply AffineAdjacentInversions.ext_entry
  funext i
  rw [Guralnick.Family.entry_formula]
  fin_cases i <;> rfl

theorem top_endpoint (c : WindowCoxeter 5) :
    c.system.simple 1 * c.system.simple 4 * c.system.simple 0 *
      AffinePermutation.longest 5 =
    Guralnick.Family.upper (by decide : 2 ≤ 2) (by decide : 1 ≤ 1)
      (by decide : 1 ≤ 2) := by
  rw [simple_zero, mul_assoc _ _ (coset 1), simple_four_mul,
    simple_one_four_mul, affine_top]
  rfl

theorem longest_length (c : WindowCoxeter 5) :
    c.system.length (AffinePermutation.longest 5) = 10 := by
  rw [c.length_formula]
  decide

theorem source_longest (c : WindowCoxeter 5) :
    (ElementaryCoxeterParabolic.longestData c (Family.source 2)).longest.val =
      AffinePermutation.longest 5 := by
  rw [FiniteBlocks.Family.source_eq_standard]
  exact ElementaryCoxeterFinite.standardFiniteLongest c
    (ElementaryCoxeterParabolic.longestData c) (by decide)

theorem finite_length_le (c : WindowCoxeter 5)
    (u : subgroup c (Family.source 2)) : c.system.length u.val ≤ 10 := by
  have h := (ElementaryCoxeterParabolic.longestData c (Family.source 2)).length_max u
  simpa [source_longest, longest_length] using h

theorem finite_length_lt (c : WindowCoxeter 5)
    (u : subgroup c (Family.source 2)) (hu : u.val ≠ AffinePermutation.longest 5) :
    c.system.length u.val < 10 := by
  have h := ElementaryCoxeterLongest.length_lt_longest c (Family.source 2)
    (ElementaryCoxeterParabolic.longestData c (Family.source 2)) u
    (by simpa [source_longest] using hu)
  simpa [source_longest, longest_length] using h

end Guralnick.SeedCosets
