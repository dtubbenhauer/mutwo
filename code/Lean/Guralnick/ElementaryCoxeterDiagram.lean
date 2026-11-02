import Guralnick.AffineReflection
import Guralnick.FidelityKL

/-!
# Diagram invariance from the defining KL properties

The generator multiplication formula follows from reduced words and the
quadratic relation. Reindexing the actual standard basis therefore commutes
with multiplication by generators and with bar. Canonical uniqueness then
proves diagram invariance without an additional literature input.
-/
noncomputable section
namespace Guralnick.ElementaryCoxeterDiagram
open Hecke Positivity CanonicalCorrection
open scoped BigOperators
variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)

@[simp] theorem standard_one : K.standard 1 = 1 := by
  simpa [word] using K.standard_reduced [] (by simp [CoxeterSystem.IsReduced])

@[simp] theorem standard_simple (i : Fin n) : K.standard (c.system.simple i) = H i := by
  simpa [word] using K.standard_reduced [i] (by simp [CoxeterSystem.IsReduced])

theorem generator_mul_of_ascent (w : AffinePermutation n) (i : Fin n)
    (h : c.system.length (c.system.simple i*w) = c.system.length w+1) :
    H i*K.standard w = K.standard (c.system.simple i*w) := by
  obtain ⟨l,hl,rfl⟩ := c.system.exists_reduced_word' w
  have hr : c.system.IsReduced (i::l) := by
    change c.system.length (c.system.simple i*c.system.wordProd l)=l.length+1
    exact h.trans (congrArg (·+1) hl)
  rw [K.standard_reduced l hl,←c.system.wordProd_cons,K.standard_reduced _ hr]
  rfl

theorem generator_mul_of_descent (w : AffinePermutation n) (i : Fin n)
    (h : c.system.length (c.system.simple i*w)+1 = c.system.length w) :
    H i*K.standard w = K.standard (c.system.simple i*w) +
      (LaurentPolynomial.T (-1)-LaurentPolynomial.T 1 : R) • K.standard w := by
  have hh : c.system.length (c.system.simple i*(c.system.simple i*w)) =
      c.system.length (c.system.simple i*w)+1 := by
    rw [c.system.simple_mul_simple_cancel_left]
    exact h.symm
  have ha := generator_mul_of_ascent K (c.system.simple i*w) i hh
  rw [c.system.simple_mul_simple_cancel_left] at ha
  rw [←ha,←mul_assoc,quadratic,add_mul,one_mul,mul_assoc]
  rw [←Algebra.smul_def,ha]

theorem finite_expansion (x : Hecke.Algebra n) :
    (∑ w ∈ (K.standard.repr x).support, K.standard.repr x w • K.standard w)=x := by
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using
    K.standard.linearCombination_repr x

variable (e : AffinePermutation n ≃* AffinePermutation n) (σ : Equiv.Perm (Fin n))
variable (hs : ∀ i, e (c.system.simple i)=c.system.simple (σ i))

include hs

theorem map_wordProd (l : List (Fin n)) :
    e (c.system.wordProd l)=c.system.wordProd (l.map σ) := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [CoxeterSystem.wordProd_cons,List.map_cons,map_mul,hs,ih]

theorem symm_simple (i : Fin n) : e.symm (c.system.simple i)=c.system.simple (σ.symm i) := by
  apply e.injective
  simp [hs]

theorem length_map (w : AffinePermutation n) : c.system.length (e w)=c.system.length w := by
  have hle (f : AffinePermutation n ≃* AffinePermutation n) (τ : Equiv.Perm (Fin n))
      (hf : ∀ i, f (c.system.simple i)=c.system.simple (τ i)) (z : AffinePermutation n) :
      c.system.length (f z) ≤ c.system.length z := by
    obtain ⟨l,hl,rfl⟩ := c.system.exists_reduced_word z
    rw [map_wordProd f τ hf]
    exact (c.system.length_wordProd_le _).trans (by simp [hl])
  exact le_antisymm (hle e σ hs w)
    (by simpa using hle e.symm σ.symm (symm_simple e σ hs) (e w))

omit hs

/-- Reindex the actual standard basis, rather than assuming an algebra action. -/
def diagramMap : Hecke.Algebra n →ₗ[R] Hecke.Algebra n :=
  K.standard.constr R (fun w => K.standard (e w))

@[simp] theorem diagramMap_standard (w : AffinePermutation n) :
    diagramMap K e (K.standard w)=K.standard (e w) := K.standard.constr_basis _ _ _

@[simp] theorem diagramMap_one : diagramMap K e 1 = 1 := by
  rw [←standard_one K,diagramMap_standard,map_one,standard_one]

include hs

@[simp] theorem diagramMap_generator (i : Fin n) : diagramMap K e (H i)=H (σ i) := by
  rw [←standard_simple K,diagramMap_standard,hs,standard_simple]

theorem diagramMap_generator_standard (i : Fin n) (w : AffinePermutation n) :
    diagramMap K e (H i*K.standard w) = H (σ i)*diagramMap K e (K.standard w) := by
  have hlen : c.system.length (c.system.simple (σ i)*e w) =
      c.system.length (c.system.simple i*w) := by
    rw [←hs,←map_mul,length_map e σ hs]
  rcases c.system.length_simple_mul w i with h|h
  · rw [generator_mul_of_ascent K w i h,diagramMap_standard,diagramMap_standard,
      generator_mul_of_ascent K (e w) (σ i) (by rw [hlen,length_map e σ hs]; exact h),
      map_mul,hs]
  · rw [generator_mul_of_descent K w i h,map_add,map_smul,diagramMap_standard,
      diagramMap_standard,generator_mul_of_descent K (e w) (σ i)
        (by rw [hlen,length_map e σ hs]; exact h),map_mul,hs]

theorem diagramMap_generator_mul (i : Fin n) (x : Hecke.Algebra n) :
    diagramMap K e (H i*x)=H (σ i)*diagramMap K e x := by
  classical
  have hx := finite_expansion K x
  rw [←hx]
  simp only [Finset.mul_sum,mul_smul_comm,map_sum,map_smul,diagramMap_generator_standard K e σ hs]

theorem diagramMap_word (l : List (Fin n)) :
    diagramMap K e (word l)=word (l.map σ) := by
  induction l with
  | nil => simpa [word] using diagramMap_one K e
  | cons i l ih =>
    change diagramMap K e (H i*word l)=H (σ i)*word (l.map σ)
    rw [diagramMap_generator_mul K e σ hs,ih]

theorem diagramMap_bar_word (l : List (Fin n)) :
    diagramMap K e (K.bar (word l))=K.bar (diagramMap K e (word l)) := by
  induction l with
  | nil => simp [word]
  | cons i l ih =>
    change diagramMap K e (K.bar (H i*word l))=K.bar (diagramMap K e (H i*word l))
    rw [map_mul,K.bar_generator,add_mul,map_add,diagramMap_generator_mul K e σ hs]
    rw [←Algebra.smul_def,map_smul,ih,diagramMap_generator_mul K e σ hs,map_mul,K.bar_generator]
    rw [add_mul,Algebra.smul_def]

theorem diagramMap_bar (x : Hecke.Algebra n) :
    diagramMap K e (K.bar x)=K.bar (diagramMap K e x) := by
  classical
  have hstd (w : AffinePermutation n) :
      diagramMap K e (K.bar (K.standard w))=K.bar (diagramMap K e (K.standard w)) := by
    obtain ⟨l,hl,rfl⟩ := c.system.exists_reduced_word' w
    rw [K.standard_reduced l hl]
    exact diagramMap_bar_word K e σ hs l
  rw [←finite_expansion K x]
  simp only [map_sum,Hecke.bar_smul,map_smul,hstd]

omit hs in
theorem diagramMap_coordinate (x : Hecke.Algebra n) (w : AffinePermutation n) :
    K.standard.repr (diagramMap K e x) (e w)=K.standard.repr x w := by
  classical
  rw [←finite_expansion K x]
  simp only [map_sum,map_smul,diagramMap_standard,Finsupp.finset_sum_apply,
    Finsupp.smul_apply,smul_eq_mul,K.standard.repr_self_apply]
  simp only [e.injective.eq_iff]

theorem diagramMap_canonical (w : AffinePermutation n) :
    diagramMap K e (K.canonical w)=K.canonical (e w) := by
  apply sub_eq_zero.mp
  apply FidelityKL.bar_fixed_positive_zero K
  · rw [map_sub,←diagramMap_bar K e σ hs,K.bar_canonical,K.bar_canonical]
  · intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    rw [map_sub,Finsupp.sub_apply,diagramMap_coordinate]
    by_cases hz : z=w
    · subst z
      rw [K.canonical_diagonal,K.canonical_diagonal,sub_self]
      intro a ha
      rfl
    · exact lowerBound_sub (K.canonical_lower z w hz)
        (K.canonical_lower (e z) (e w) (fun h => hz (e.injective h)))

omit hs in
/-- Every generator-preserving group automorphism preserves the ordinary
canonical coefficients. The old literature field is now a theorem. -/
theorem diagramInvariance : AffineReflection.DiagramInvarianceInput K := by
  intro e σ hs y w
  rw [←diagramMap_canonical K e σ hs w,diagramMap_coordinate]

#print axioms diagramInvariance
end Guralnick.ElementaryCoxeterDiagram
