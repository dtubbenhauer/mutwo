import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-!
# A generic passage from row sums to actual first cohomology

This file uses mathlib's `groupCohomology A 1` for actual representations.
Its parameters `μ`, `DoubledRowSum` and `PrimeFieldTransfer` deliberately
form a generic intermediate implication; they are not definitions of the
manuscript's coefficients or assumptions classified as literature results.

The later module `LiteratureTransfer` constructs the named highest-weight
family and proves `PrimeFieldTransfer` for actual fixed-w0 KL coefficients
from the precise general representation-theoretic inputs. `WebProof`
proves the required row sum from the original six-map calculation.
`AbsoluteIrreducibility` proves the scalar-extension criterion and formulates
the all-field conjecture. Thus the final theorem has only the explicit
general literature/framework hypotheses, whereas the theorems in this
intermediate file retain the abstract row and transfer parameters.

See `literature-inputs.md` for the remaining external theorems and
`formalization-review.md` for semantic scope. Cohomology is never defined
as a desired numerical value, and the final result remains conditional on
the stated general inputs.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Guralnick
namespace Cohomology

/-- First cohomology of the actual representation, computed by mathlib's
inhomogeneous cochain complex. -/
abbrev H1 {k G : Type} [Field k] [Group G] (A : Rep k G) : ModuleCat k :=
  groupCohomology A 1

/-- The dimension used in the conjecture. Our transfer hypothesis separately
requires `FiniteDimensional k (H1 A)`, ruling out the infinite-dimensional
`finrank = 0` convention for all constructed witnesses. -/
def h1Dimension {k G : Type} [Field k] [Group G] (A : Rep k G) : ℕ :=
  Module.finrank k (H1 A)

/-- The source is the one-dimensional trivial representation, not another
varying irreducible representation. This is mathlib's proved Ext comparison. -/
def h1IsoExtFromTrivial {k G : Type} [Field k] [Group G] (A : Rep k G) :
    H1 A ≅ ((Ext k (Rep k G) 1).obj
      (Opposite.op (Rep.trivial k G k))).obj A := by
  classical
  exact groupCohomologyIsoExt A 1

/-- Faithfulness means that distinct group elements give distinct linear maps. -/
def Faithful {k G : Type} [Field k] [Group G] (A : Rep k G) : Prop :=
  Function.Injective A.ρ

/-- Nonzero and without a proper nonzero invariant linear subspace. -/
def Irreducible {k G : Type} [Field k] [Group G] (A : Rep k G) : Prop :=
  Nontrivial A ∧ ∀ V : Submodule k A,
    (∀ g : G, ∀ x : A, x ∈ V → A.ρ g x ∈ V) → V = ⊥ ∨ V = ⊤

/-- The module conditions in the algebraically closed-field conjecture. -/
def Admissible {k G : Type} [Field k] [Group G] (A : Rep k G) : Prop :=
  FiniteDimensional k A ∧ Faithful A ∧ Irreducible A

/-- A bound uniform in the finite group, algebraically closed field,
characteristic and faithful finite-dimensional irreducible representation. -/
def UniformH1Bound (C : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G : Type) [Group G] [Finite G] (A : Rep k G),
    Admissible A → h1Dimension A ≤ C

/-- The algebraically closed-field instance of Guralnick's conjecture. -/
def AlgebraicallyClosedBoundedness : Prop := ∃ C : ℕ, UniformH1Bound C

/-- The actual projective special linear group over the prime field. -/
abbrev PSL (m p : ℕ) :=
  Matrix.ProjectiveSpecialLinearGroup (Fin (2 * m + 1)) (ZMod p)

/-- The actual algebraic closure of the prime field. -/
abbrev PrimeClosure (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

/-- Numerical row-sum input, with one-based `j` and no natural-number division.
This is equivalent to the manuscript's sum `choose (m+1) 2` for `m >= 2`. -/
def DoubledRowSum (μ : ℕ → ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    2 * (∑ j : Fin m, μ m (j.val + 1)) = m * (m + 1)

/-- Explicit application hypothesis. For each rank and every sufficiently
large prime satisfying the BNP bound, there are actual representations of
`PSL_(2m+1)(F_p)` whose actual first-cohomology dimensions equal `μ`.
The type does not identify `μ` with KL coefficients or these representations
with the manuscript's named highest-weight modules. Those identifications
and the published transfer theorems remain obligations for an application.
No statement in this file supplies this hypothesis by an axiom. -/
def PrimeFieldTransfer (μ : ℕ → ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ p₀ : ℕ,
    ∀ (p : ℕ) (hp : p.Prime), p₀ ≤ p → 5 * (2 * m) ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∃ A : Fin m → Rep (PrimeClosure p) (PSL m p),
        (∀ j, Admissible (A j)) ∧
        (∀ j, FiniteDimensional (PrimeClosure p) (H1 (A j))) ∧
        (∀ j, h1Dimension (A j) = μ m (j.val + 1))

/-- Averaging written as a strict-bound contradiction. -/
theorem exists_entry_gt_of_row {m C : ℕ} (f : Fin m → ℕ)
    (hm : 0 < m) (hC : 2 * C < m + 1)
    (hrow : 2 * (∑ j : Fin m, f j) = m * (m + 1)) :
    ∃ j : Fin m, C < f j := by
  classical
  by_contra h
  have hle : ∀ j : Fin m, f j ≤ C := by
    intro j
    exact Nat.le_of_not_gt (fun hj => h ⟨j, hj⟩)
  have hsum : (∑ j : Fin m, f j) ≤ m * C := by
    calc
      (∑ j : Fin m, f j) ≤ ∑ _j : Fin m, C :=
        Finset.sum_le_sum (fun j _ => hle j)
      _ = m * C := by simp
  nlinarith

/-- The manuscript's rank-by-rank conclusion, still conditional on both
major inputs. `m / 2 + 1` is exactly `ceil((m+1)/2)` for natural `m`.
The same family has the exact doubled H¹ row sum at every eligible prime. -/
theorem rowSum_and_lowerBound (μ : ℕ → ℕ → ℕ)
    (hrow : DoubledRowSum μ) (htransfer : PrimeFieldTransfer μ)
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ ≤ p → 5*(2*m) ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∃ A : Fin m → Rep (PrimeClosure p) (PSL m p),
        (∀ j, Admissible (A j)) ∧
        (∀ j, FiniteDimensional (PrimeClosure p) (H1 (A j))) ∧
        2*(∑ j : Fin m, h1Dimension (A j)) = m*(m+1) ∧
        ∃ j : Fin m, m / 2 + 1 ≤ h1Dimension (A j) := by
  classical
  obtain ⟨p₀, hT⟩ := htransfer m hm
  refine ⟨p₀, ?_⟩
  intro p hp hp₀ hBNP
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA, hfinite, hdim⟩ := hT p hp hp₀ hBNP
  have hsum : 2*(∑ j : Fin m, h1Dimension (A j)) = m*(m+1) := by
    simpa only [hdim] using hrow m hm
  obtain ⟨j, hj⟩ := exists_entry_gt_of_row (m := m) (C := m / 2)
    (fun j => h1Dimension (A j)) (by omega) (by omega) hsum
  exact ⟨A, hA, hfinite, hsum, j, by omega⟩

/-- The conditional inputs give actual first-cohomology counterexamples over
prime fields of arbitrarily large characteristic. The final witness includes
finite dimensionality of its genuine cohomology vector space. -/
theorem exists_PSL_counterexample (μ : ℕ → ℕ → ℕ)
    (hrow : DoubledRowSum μ) (htransfer : PrimeFieldTransfer μ)
    (C lowerPrimeBound : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ p : ℕ, ∃ hp : p.Prime,
      lowerPrimeBound ≤ p ∧
      letI : Fact p.Prime := ⟨hp⟩
      ∃ A : Rep (PrimeClosure p) (PSL m p),
        Admissible A ∧ FiniteDimensional (PrimeClosure p) (H1 A) ∧
        C < h1Dimension A := by
  classical
  let m := 2 * C + 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  obtain ⟨p₀, htransfer_m⟩ := htransfer m hm
  obtain ⟨p, hbound, hp⟩ :=
    Nat.exists_infinite_primes (max p₀ (max (5 * (2 * m)) lowerPrimeBound))
  have hp₀ : p₀ ≤ p := le_trans (le_max_left _ _) hbound
  have hBNP : 5 * (2 * m) ≤ p :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hbound
  have hlower : lowerPrimeBound ≤ p :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hbound
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA, hfiniteH1, hdim⟩ := htransfer_m p hp hp₀ hBNP
  obtain ⟨j, hj⟩ := exists_entry_gt_of_row (m := m) (C := C)
    (fun j : Fin m => μ m (j.val + 1))
    (by omega) (by dsimp [m]; omega) (hrow m hm)
  refine ⟨m, hm, p, hp, hlower, A j, hA j, hfiniteH1 j, ?_⟩
  simpa only [hdim j] using hj

/-- A formal implication to the negation of a bound on actual `H¹` dimensions.
Both substantial inputs are explicit hypotheses. -/
theorem not_algebraicallyClosedBoundedness (μ : ℕ → ℕ → ℕ)
    (hrow : DoubledRowSum μ) (htransfer : PrimeFieldTransfer μ) :
    ¬ AlgebraicallyClosedBoundedness := by
  rintro ⟨C, hC⟩
  obtain ⟨m, _hm, p, hp, _hlower, A, hA, _hfiniteH1, hlarge⟩ :=
    exists_PSL_counterexample μ hrow htransfer C 0
  letI : Fact p.Prime := ⟨hp⟩
  have hsmall := hC (PrimeClosure p) (PSL m p) A hA
  exact (Nat.not_lt_of_ge hsmall) hlarge

end Cohomology
end Guralnick
