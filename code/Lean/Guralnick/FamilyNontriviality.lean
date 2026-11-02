import Guralnick.HighestWeight
import Mathlib.Algebra.Field.Power

/-!
# Nontrivial finite action from the family's highest-weight vector

The diagonal element with two entries equal to `-1`, at coordinates `m-1`
and `m`, belongs to the prime-field special linear group. Its character on
the actual highest-weight vector is `-1`: the relevant weight coordinates
are `(1, 0)` for `j < m` and `(p-2, 0)` for `j = m`.

Thus nontriviality of this family's finite restriction is elementary. It
does not require the separation-of-weights part of Steinberg's theorem.
-/

noncomputable section
open scoped BigOperators

namespace Guralnick.HighestWeight

private def pairSigns (k : Type) [Field k] {n : ℕ} (a b : Fin n) (i : Fin n) : kˣ :=
  (if i = a then -1 else 1) * (if i = b then -1 else 1)

private theorem pairSigns_prod (k : Type) [Field k] {n : ℕ} (a b : Fin n) :
    ∏ i, pairSigns k a b i = 1 := by
  unfold pairSigns
  rw [Finset.prod_mul_distrib]
  simp

private theorem pairSigns_character (k : Type) [Field k] {n : ℕ}
    (wt : Fin n → ℤ) (a b : Fin n) :
    character wt (pairSigns k a b) = (-1 : k) ^ wt a * (-1 : k) ^ wt b := by
  unfold character pairSigns
  simp only [mul_zpow, Finset.prod_mul_distrib]
  have h (c : Fin n) :
      (∏ i, (if i = c then (-1 : kˣ) else 1) ^ wt i) = (-1 : kˣ) ^ wt c := by
    trans ∏ i, if i = c then (-1 : kˣ) ^ wt i else 1
    · apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> simp_all
    · simp
  rw [h, h]
  simp

private theorem pairSigns_map {k k' : Type} [Field k] [Field k']
    (f : k →+* k') {n : ℕ} (a b : Fin n) :
    Matrix.SpecialLinearGroup.map f (torusElement (pairSigns k a b) (pairSigns_prod k a b)) =
      torusElement (pairSigns k' a b) (pairSigns_prod k' a b) := by
  apply Subtype.ext
  ext i j
  change f (Matrix.diagonal (fun i => (pairSigns k a b i : k)) i j) =
    Matrix.diagonal (fun i => (pairSigns k' a b i : k')) i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    unfold pairSigns
    simp only [Units.val_mul, map_mul]
    congr 1 <;> split_ifs <;> simp
  · simp [hij]

/-- The finite restriction of every actual highest-weight module with a
family weight acts nontrivially, throughout the original range `p > 2m+1`.
Only its highest-weight vector is needed, not rational or finite-group
irreducibility and not any literature input. -/
theorem family_restrictPrime_nontrivial {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) [Fact p.Prime]
    (hp : 2 * m + 1 < p)
    (A : Rep (Cohomology.PrimeClosure p) (SL (2 * m + 1) (Cohomology.PrimeClosure p)))
    (hw : HasHighestWeight A (Weights.familyWeight m j p).val) :
    (restrictPrime (2 * m + 1) p A).ρ ≠ 1 := by
  let k := Cohomology.PrimeClosure p
  let a : Fin (2 * m + 1) := ⟨m - 1, by omega⟩
  let b : Fin (2 * m + 1) := ⟨m, by omega⟩
  have ha : Weights.coordinate m j p a = if j = m then (p : ℤ) - 2 else 1 := by
    dsimp [a, Weights.coordinate, Weights.leftCoordinate]
    split_ifs <;> omega
  have hb : Weights.coordinate m j p b = 0 := by
    simp [b, Weights.coordinate]
  have hodd : Odd ((p : ℤ) - 2) := by
    obtain ⟨r, hr⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    refine ⟨(r : ℤ) - 1, ?_⟩
    omega
  have hchar : character (Weights.familyWeight m j p).val (pairSigns k a b) = -1 := by
    rw [pairSigns_character]
    change (-1 : k) ^ Weights.coordinate m j p a *
      (-1 : k) ^ Weights.coordinate m j p b = -1
    rw [ha, hb]
    split_ifs <;> simp [hodd.neg_one_zpow]
  obtain ⟨v, hv, _, htorus⟩ := hw
  have hweight := htorus (pairSigns k a b) (pairSigns_prod k a b)
  rw [hchar] at hweight
  intro htrivial
  let g : SL (2 * m + 1) (ZMod p) :=
    torusElement (pairSigns (ZMod p) a b) (pairSigns_prod (ZMod p) a b)
  have hact := congrArg (fun ρ => ρ g v) htrivial
  change A.ρ (Matrix.SpecialLinearGroup.map (algebraMap (ZMod p) k) g) v = v at hact
  dsimp [g] at hact
  rw [pairSigns_map] at hact
  have hscalar : (-1 : k) • v = (1 : k) • v := by
    rw [one_smul]
    exact hweight.symm.trans hact
  have heq : (-1 : k) = 1 := smul_left_injective k hv hscalar
  letI : Fact (2 < p) := ⟨by omega⟩
  exact CharP.neg_one_ne_one k p heq

end Guralnick.HighestWeight
