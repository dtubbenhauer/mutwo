import Guralnick.SchurCornerEigen
import Guralnick.HeckeEigenCoordinates

/-!
# Canonical corner support from canonical refinement span

The refinement input puts every canonical element with the prescribed
descents in the actual spherical eigencorner. Removing a maximal-length
canonical term of an eigenvector then proves the converse support
statement by induction on its finite canonical support.
-/

noncomputable section
namespace Guralnick.CanonicalSchurFromRefinement
open Hecke ParabolicWeb CanonicalSchur HeckeRefinement
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

theorem compatibility_of_top
    (hcanonical : ∀ (I J : Index n) (w : AffinePermutation n),
      DoubleMaximal c I J w → K.canonical w ∈ corner I J)
    (htop : ∀ (x : Hecke.Algebra n) (I J : Index n), x ∈ corner I J →
      ∀ w, K.canonical.repr x w ≠ 0 →
      (∀ z ∈ (K.canonical.repr x).support, c.system.length z ≤ c.system.length w) →
      DoubleMaximal c I J w) : Compatibility K := by
  classical
  constructor
  intro I J x hx w hw
  have aux : ∀ (S : Finset (AffinePermutation n)) (x : Hecke.Algebra n),
      (K.canonical.repr x).support = S → x ∈ corner I J →
      ∀ w, K.canonical.repr x w ≠ 0 → DoubleMaximal c I J w := by
    intro S
    induction' S using Finset.strongInductionOn with S ih
    intro x hS hx w hw
    have hwS : w ∈ S := hS ▸ Finsupp.mem_support_iff.mpr hw
    obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image S c.system.length ⟨w,hwS⟩
    have hz' : z ∈ (K.canonical.repr x).support := hS.symm ▸ hz
    have hzmax : DoubleMaximal c I J z := htop x I J hx z
      (Finsupp.mem_support_iff.mp hz') (fun u hu => hmax u (hS ▸ hu))
    by_cases hwz : w = z
    · exact hwz.symm ▸ hzmax
    · let x' : Hecke.Algebra n := x + (-K.canonical.repr x z) • K.canonical z
      have he : K.canonical.repr x' = (K.canonical.repr x).erase z := by
        change K.canonical.repr (x + (-K.canonical.repr x z) • K.canonical z) = _
        rw [map_add, map_smul, Basis.repr_self]
        apply Finsupp.ext
        intro u
        simp only [Finsupp.add_apply,
          Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul]
        by_cases huz : u=z
        · subst u
          simp
        · simp [huz,Ne.symm huz]
      have hsupport : (K.canonical.repr x').support = S.erase z := by
        rw [he,Finsupp.support_erase,hS]
      have hx' : x' ∈ corner I J := by
        change x + (-K.canonical.repr x z) • K.canonical z ∈ corner I J
        apply Submodule.add_mem (corner I J) hx
        exact Submodule.smul_mem (corner I J) (-K.canonical.repr x z) (hcanonical I J z hzmax)
      apply ih (S.erase z) (Finset.erase_ssubset hz) x' hsupport hx' w
      rw [he,Finsupp.erase_ne hwz]
      exact hw
  exact aux _ x rfl hx w hw

theorem canonical_mem_corner
    (D : ∀ I : Index n, LongestData c I)
    (B : CanonicalRefinement.StandardCompatibility K D)
    (I J : Index n) (w : AffinePermutation n) (hw : DoubleMaximal c I J w) :
    K.canonical w ∈ corner I J := by
  letI := (D I).finite
  letI := (D J).finite
  exact schurCorner_le_corner K I J (B.canonical_span I J w hw)

/-- Canonical refinement span already implies canonical corner support.
No positivity, geometric realization, or second Schur-basis input is used. -/
def toCompatibility (D : ∀ I : Index n, LongestData c I)
    (B : CanonicalRefinement.StandardCompatibility K D) : Compatibility K :=
  compatibility_of_top K (canonical_mem_corner K D B)
    (HeckeEigenCoordinates.eigen_top_doubleMaximal K)

#print axioms toCompatibility

end Guralnick.CanonicalSchurFromRefinement
