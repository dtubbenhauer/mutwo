import Guralnick.CanonicalOneLinePatterns
import Guralnick.PolynomialWebLiterature

/-!
# The two actual retained-line indices in the first example

The window `[7,5,4,3,-4]` is specified as a balanced periodic permutation.
Its inverse winding counts and finite descents identify the leading index
of the retained-line web. The reflected index includes winding reversal.
All finite checks below produce kernel proof terms.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace Guralnick.SeedOneLineIndex
open Hecke WindowPacketMatrix CanonicalMatrix

private def certificate : WindowCertificate 5 where
  residue := ![1,4,3,2,0]
  inverse := ![4,0,3,2,1]
  winding := ![1,0,0,0,-1]

/-- The actual affine permutation with window `[7,5,4,3,-4]`. -/
def strong : AffinePermutation 5 := certificate.toAffine (by decide)

theorem strong_window : strong.window = [7,5,4,3,-4] := by decide

theorem strong_inverse_window : strong⁻¹.window = [10,-4,4,3,2] := by decide

theorem strong_supported : Supported strong := by
  unfold Supported
  decide

theorem strong_entries : entries 2 strong = ![![1,0,1], ![0,1,0], ![0,2,0]] := by
  decide

theorem strong_parameters :
    let A := packetMatrix 2 strong strong_supported
    A.rank = 1 ∧ A.a = 1 ∧ A.s = 0 ∧ A.beta = 0 ∧ A.delta = 1 := by
  decide

theorem strong_doubleMaximal (c : WindowCoxeter 5) :
    CanonicalSchur.DoubleMaximal c (ParabolicWeb.Family.output 2)
      (ParabolicWeb.Family.source 2) strong := by
  constructor
  · intro b hb
    have hbs : b = 1 ∨ b = 4 := by
      fin_cases b <;>
        simp_all [ParabolicWeb.Family.output, ParabolicWeb.Family.outputSet,
          ParabolicWeb.Family.sourceSet, ParabolicWeb.Family.cyclicSet]
    rcases hbs with rfl | rfl
    · rw [← c.system.isRightDescent_inv_iff, c.finite_descent _ 0 1 (by decide)]
      decide
    · rw [← c.system.isRightDescent_inv_iff, c.finite_descent _ 3 4 (by decide)]
      decide
  · intro b hb
    have hb0 : b ≠ 0 := by
      simpa [ParabolicWeb.Family.source, ParabolicWeb.Family.sourceSet] using hb
    fin_cases b
    · exact (hb0 rfl).elim
    · change c.system.IsRightDescent strong (1 : Fin 5)
      rw [c.finite_descent _ 0 1 (by decide)]; decide
    · change c.system.IsRightDescent strong (2 : Fin 5)
      rw [c.finite_descent _ 1 2 (by decide)]; decide
    · change c.system.IsRightDescent strong (3 : Fin 5)
      rw [c.finite_descent _ 2 3 (by decide)]; decide
    · change c.system.IsRightDescent strong (4 : Fin 5)
      rw [c.finite_descent _ 3 4 (by decide)]; decide

theorem strong_length (c : WindowCoxeter 5) : c.system.length strong = 15 := by
  rw [c.length_formula]
  decide

theorem longest_length (c : WindowCoxeter 5) :
    c.system.length (AffinePermutation.longest 5) = 10 := by
  rw [c.length_formula]
  decide

theorem strong_longer_than_source (c : WindowCoxeter 5) :
    c.system.length (AffinePermutation.longest 5) < c.system.length strong := by
  rw [strong_length, longest_length]
  decide

theorem strong_ne_reflect : strong ≠ AffineReflection.reflect strong := by
  intro h
  have he := congrArg (fun w : AffinePermutation 5 => w.entry 0) h
  have hn : strong.entry 0 ≠ (AffineReflection.reflect strong).entry 0 := by decide
  exact hn he

theorem strong_ne_source : strong ≠ AffinePermutation.longest 5 := by
  intro h
  have he := congrArg (fun w : AffinePermutation 5 => w.entry 0) h
  have hn : strong.entry 0 ≠ (AffinePermutation.longest 5).entry 0 := by decide
  exact hn he

theorem strong_ne_family (c : WindowCoxeter 5) (j : Fin 2) :
    strong ≠ Family.upper (by decide : 2 ≤ 2)
      (show 1 ≤ j.val+1 by omega) (show j.val+1 ≤ 2 by omega) := by
  intro he
  have hgap := Hecke.family_length_gap (by decide : 2 ≤ 2)
    (show 1 ≤ j.val+1 by omega) (show j.val+1 ≤ 2 by omega) c
  rw [← he, strong_length, longest_length] at hgap
  fin_cases j <;> norm_num [gapFormula] at hgap

theorem reflected_length (c : WindowCoxeter 5) :
    c.system.length (AffineReflection.reflect strong) = 15 := by
  rw [AffineReflection.length_reflect (by decide), strong_length]

theorem reflected_ne_family (c : WindowCoxeter 5) (j : Fin 2) :
    AffineReflection.reflect strong ≠ Family.upper (by decide : 2 ≤ 2)
      (show 1 ≤ j.val+1 by omega) (show j.val+1 ≤ 2 by omega) := by
  intro he
  have hgap := Hecke.family_length_gap (by decide : 2 ≤ 2)
    (show 1 ≤ j.val+1 by omega) (show j.val+1 ≤ 2 by omega) c
  rw [← he, reflected_length, longest_length] at hgap
  fin_cases j <;> norm_num [gapFormula] at hgap

theorem reflected_ne_source :
    AffineReflection.reflect strong ≠ AffinePermutation.longest 5 := by
  intro h
  apply strong_ne_source
  simpa using congrArg AffineReflection.reflect h

/-- The integral one-line morphism is the canonical element of this window. -/
theorem oneLine_eq_canonical (T : Theory 5) (W : PolynomialWebLiterature T) :
    CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
      (1 : Fin 5) (2 : Fin 5) = T.kl.canonical strong := by
  have h := CanonicalOneLinePatterns.strong_canonical (by decide : 2 ≤ 2)
    T W.toWebLiterature strong strong_supported (strong_doubleMaximal T.coxeter)
    strong_parameters.2.1 strong_parameters.2.2.1 strong_parameters.2.2.2.1
  have hr : CanonicalOneLinePatterns.rankNode (m := 2) strong strong_supported = (1 : Fin 5) :=
    Fin.ext strong_parameters.1
  simpa only [hr] using h

theorem reflected_oneLine_eq_canonical (T : Theory 5) (W : PolynomialWebLiterature T) :
    ElementaryCoxeterDiagram.diagramMap T.kl (AffineReflection.equiv 5)
      (CanonicalChains.oneLine T.kl W.longest W.parabolic (by decide)
        (1 : Fin 5) (2 : Fin 5)) =
      T.kl.canonical (AffineReflection.reflect strong) := by
  rw [oneLine_eq_canonical]
  exact ElementaryCoxeterDiagram.diagramMap_canonical T.kl (AffineReflection.equiv 5)
    (AffineReflection.nodeEquiv 5) (AffineReflection.reflect_simple (by decide) T.coxeter)
    strong

end Guralnick.SeedOneLineIndex
