import Guralnick.SeedDecompositionBounds
import Guralnick.SeedOneLineIndex
import Guralnick.FidelityKL

/-! # The exact five-term canonical expansion of the first web

This is the manuscript's seed expansion in the actual presented affine
Hecke algebra.  The two one-line terms have explicitly checked affine
indices, and their multiplicity one follows from the gallery polynomial
and the constant-term argument, not from a supplied decomposition.
-/

noncomputable section
set_option maxHeartbeats 1200000
namespace Guralnick.SeedDecomposition
open Hecke ParabolicWeb Positivity CanonicalRowSum CanonicalMultiplicityBounds
open WindowPacketMatrix CanonicalMatrix SeedOneLineIndex

variable (T : Hecke.Theory 5) (W : PolynomialWebLiterature T)

private theorem origin_coordinate_zero (w : AffinePermutation 5)
    (hl : T.coxeter.system.length (AffinePermutation.longest 5) < T.coxeter.system.length w) :
    T.kl.standard.repr (T.kl.canonical (AffinePermutation.longest 5)) w = 0 := by
  by_contra hn
  have he := FidelityKL.bruhat_eq_of_length_le (T.kl.canonical_support w _ hn)
    (Nat.le_of_lt hl)
  rw [he] at hl
  exact (Nat.lt_irrefl _ hl)

theorem strong_multiplicity :
    T.kl.canonical.repr (W.toWebLiterature.raw (m := 2)) strong = 1 := by
  apply multiplicity_one_of_constant T W.toWebLiterature strong strong_ne_source
    (origin_coordinate_zero T strong (strong_longer_than_source T.coxeter))
  exact strong_standard_constant T W.toWebLiterature strong strong_supported
    (strong_doubleMaximal T.coxeter) strong_parameters.1
    (Or.inl ⟨strong_parameters.2.1, strong_parameters.2.2.1,
      strong_parameters.2.2.2.1, strong_parameters.2.2.2.2⟩)

theorem reflected_strong_multiplicity :
    T.kl.canonical.repr (W.toWebLiterature.raw (m := 2))
      (AffineReflection.reflect strong) = 1 := by
  apply multiplicity_one_of_constant T W.toWebLiterature _ reflected_ne_source
    (origin_coordinate_zero T _ (by rw [longest_length, reflected_length]; decide))
  apply strong_standard_constant T W.toWebLiterature _
    (PacketReflection.supported_reflect strong_supported)
    (PacketReflection.doubleMaximal_reflect (by decide : 2 ≤ 2) T.coxeter strong
      (strong_doubleMaximal T.coxeter))
  · rw [PacketReflection.rank_reflect, strong_parameters.1]
  · right
    have h := PacketReflection.parameters_reflect 2 strong strong_supported
    dsimp only at h
    have hp := strong_parameters
    dsimp only at hp
    rcases h with ⟨_, ha, hs, hb, hd⟩
    exact ⟨by change _ = 0; omega, by change _ = 1; omega,
      by change _ = 0; omega, by change _ = 1; omega⟩

theorem family_multiplicity (j : Fin 2) :
    T.kl.canonical.repr (W.toWebLiterature.raw (m := 2))
      (familyIndex (by decide : 2 ≤ 2) j) = 1 :=
  CanonicalRowSum.raw_family_multiplicity_one (m := 2) T.kl W.longest W.parabolic
    T.positivity (by decide)
    (W.toWebLiterature.marked_coordinate (by decide : 2 ≤ 2) T)
    (W.toWebLiterature.auxiliary_family_bound (by decide : 2 ≤ 2) T) j

/-- The uniform six-position classification specializes to exactly these
five actual affine permutations. -/
theorem support_five (w : AffinePermutation 5)
    (hne : T.kl.canonical.repr (W.toWebLiterature.raw (m := 2)) w ≠ 0) :
    w = familyIndex (by decide : 2 ≤ 2) (0 : Fin 2) ∨
    w = familyIndex (by decide : 2 ≤ 2) (1 : Fin 2) ∨
    w = strong ∨ w = AffineReflection.reflect strong ∨
    w = AffinePermutation.longest 5 := by
  by_cases hb : w = AffinePermutation.longest 5
  · exact Or.inr (Or.inr (Or.inr (Or.inr hb)))
  by_cases hf : ∃ j : Fin 2, w = familyIndex (by decide : 2 ≤ 2) j
  · obtain ⟨j, hj⟩ := hf
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
  have hoff : ∀ j : Fin 2, w ≠ familyIndex (by decide : 2 ≤ 2) j := by
    simpa only [not_exists] using hf
  have hw := auxiliary_word T W.toWebLiterature w hne hb hoff
  dsimp only [PolynomialWebLiterature.toWebLiterature] at hw
  rw [oneLine_eq_canonical T W] at hw
  rcases hw with hw | hw
  · exact Or.inr (Or.inr (Or.inl (T.kl.canonical.injective hw).symm))
  · have he := congrArg AffineReflection.reflect (T.kl.canonical.injective hw)
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using he.symm))))

/-- The exact canonical expansion in Lemma `seed-expansion` of the paper. -/
theorem canonical_expansion :
    ParabolicWeb.Family.raw (m := 2) T.kl W.longest W.parabolic =
      T.kl.canonical (familyIndex (by decide : 2 ≤ 2) (1 : Fin 2)) +
      T.kl.canonical (familyIndex (by decide : 2 ≤ 2) (0 : Fin 2)) +
      T.kl.canonical strong + T.kl.canonical (AffineReflection.reflect strong) +
      CanonicalCorrection.correction 2 • T.kl.canonical (AffinePermutation.longest 5) := by
  classical
  have h01 : familyIndex (by decide : 2 ≤ 2) (0 : Fin 2) ≠
      familyIndex (by decide : 2 ≤ 2) (1 : Fin 2) := by
    intro he
    have hh := familyIndex_injective (by decide : 2 ≤ 2) he
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  have h0b : familyIndex (by decide : 2 ≤ 2) (0 : Fin 2) ≠ AffinePermutation.longest 5 := by
    simpa only [CanonicalSpherical.index_zero] using
      (CanonicalSpherical.family_disjoint (r := 0) (by decide : 2 ≤ 2)
        (by decide : 1 ≤ 1) (by decide : 1 ≤ 2))
  have h1b : familyIndex (by decide : 2 ≤ 2) (1 : Fin 2) ≠ AffinePermutation.longest 5 := by
    simpa only [CanonicalSpherical.index_zero] using
      (CanonicalSpherical.family_disjoint (r := 0) (by decide : 2 ≤ 2)
        (by decide : 1 ≤ 2) (by decide : 2 ≤ 2))
  have he0 := strong_ne_family T.coxeter (0 : Fin 2)
  have he1 := strong_ne_family T.coxeter (1 : Fin 2)
  have hd0 := reflected_ne_family T.coxeter (0 : Fin 2)
  have hd1 := reflected_ne_family T.coxeter (1 : Fin 2)
  change strong ≠ familyIndex (by decide : 2 ≤ 2) (0 : Fin 2) at he0
  change strong ≠ familyIndex (by decide : 2 ≤ 2) (1 : Fin 2) at he1
  change AffineReflection.reflect strong ≠ familyIndex (by decide : 2 ≤ 2) (0 : Fin 2) at hd0
  change AffineReflection.reflect strong ≠ familyIndex (by decide : 2 ≤ 2) (1 : Fin 2) at hd1
  apply T.kl.canonical.repr.injective
  change T.kl.canonical.repr (W.toWebLiterature.raw (m := 2)) = _
  apply Finsupp.ext
  intro w
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, Basis.repr_self, Finsupp.single_apply]
  by_cases h0 : w = familyIndex (by decide : 2 ≤ 2) (0 : Fin 2)
  · subst w
    rw [family_multiplicity T W]
    simp [h01.symm, he0, hd0, h0b.symm]
  by_cases h1 : w = familyIndex (by decide : 2 ≤ 2) (1 : Fin 2)
  · subst w
    rw [family_multiplicity T W]
    simp [h01, he1, hd1, h1b.symm]
  by_cases he : w = strong
  · subst w
    rw [strong_multiplicity T W]
    simp [he0.symm, he1.symm, strong_ne_reflect.symm, strong_ne_source.symm]
  by_cases hd : w = AffineReflection.reflect strong
  · subst w
    rw [reflected_strong_multiplicity T W]
    simp [hd0.symm, hd1.symm, strong_ne_reflect, reflected_ne_source.symm]
  by_cases hb : w = AffinePermutation.longest 5
  · subst w
    rw [origin_multiplicity T W.toWebLiterature]
    simp [h0b, h1b, strong_ne_source, reflected_ne_source]
  have hz : T.kl.canonical.repr (W.toWebLiterature.raw (m := 2)) w = 0 := by
    by_contra hn
    rcases support_five T W w hn with h | h | h | h | h
    · exact h0 h
    · exact h1 h
    · exact he h
    · exact hd h
    · exact hb h
  rw [hz]
  simp [Ne.symm h0, Ne.symm h1, Ne.symm he, Ne.symm hd, Ne.symm hb]

/-- The same identity with the two actual retained-line morphisms shown,
so that each term can be matched directly with the manuscript's diagram. -/
theorem web_expansion :
    ParabolicWeb.Family.raw (m := 2) T.kl W.longest W.parabolic =
      T.kl.canonical (familyIndex (by decide : 2 ≤ 2) (1 : Fin 2)) +
      T.kl.canonical (familyIndex (by decide : 2 ≤ 2) (0 : Fin 2)) +
      CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
        (1 : Fin 5) (2 : Fin 5) +
      ElementaryCoxeterDiagram.diagramMap T.kl (AffineReflection.equiv 5)
        (CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
          (1 : Fin 5) (2 : Fin 5)) +
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : Hecke.R) •
        T.kl.canonical (AffinePermutation.longest 5) := by
  rw [reflected_oneLine_eq_canonical, oneLine_eq_canonical,
    ← CanonicalCorrection.correction_two]
  exact canonical_expansion T W

end Guralnick.SeedDecomposition
