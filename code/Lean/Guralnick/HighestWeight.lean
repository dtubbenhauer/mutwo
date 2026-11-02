import Guralnick.Cohomology
import Guralnick.Weights
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Highest weights as conditions on actual representations of SL

The diagonal torus and upper unipotent subgroup are defined by their
matrices. A highest-weight vector is an actual nonzero vector fixed by the
upper unipotents and with the specified torus character. This supplies a
semantic target for the generic highest-weight theorems; a weight is not
merely a label on an arbitrary finite-group representation.
-/

noncomputable section
namespace Guralnick.HighestWeight
open scoped BigOperators

variable {k : Type} [Field k] {n : ℕ}

abbrev SL (n : ℕ) (k : Type) [Field k] := Matrix.SpecialLinearGroup (Fin n) k

def torusElement (t : Fin n → kˣ) (ht : ∏ i, t i = 1) : SL n k :=
  ⟨Matrix.diagonal (fun i => (t i : k)), by
    rw [Matrix.det_diagonal]
    have h := congrArg (fun u : kˣ => (u : k)) ht
    simpa using h⟩

def character (wt : Fin n → ℤ) (t : Fin n → kˣ) : k :=
  ((∏ i, (t i) ^ (wt i) : kˣ) : k)

def UpperUnipotent (g : SL n k) : Prop :=
  (∀ i j : Fin n, j < i → g i j = 0) ∧ ∀ i : Fin n, g i i = 1

def HasHighestWeight (A : Rep k (SL n k)) (wt : Fin n → ℤ) : Prop :=
  ∃ v : A, v ≠ 0 ∧
    (∀ g : SL n k, UpperUnipotent g → A.ρ g v = v) ∧
    ∀ (t : Fin n → kˣ) (ht : ∏ i, t i = 1),
      A.ρ (torusElement t ht) v = character wt t • v

/-- The representation is an actual finite-dimensional irreducible module,
with an actual highest-weight vector. Polynomial/rational action is an
additional condition supplied in `RationalCohomology.lean`. -/
def SimpleHighestWeight (A : Rep k (SL n k)) (wt : Fin n → ℤ) : Prop :=
  FiniteDimensional k A ∧ Cohomology.Irreducible A ∧ HasHighestWeight A wt

theorem character_scalar (wt : Weights.RootLattice n) (a : kˣ) :
    character wt.val (fun _ => a) = 1 := by
  have hs : ∀ s : Finset (Fin n), (∏ i ∈ s, a ^ wt.val i) = a ^ (∑ i ∈ s, wt.val i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add]
  unfold character
  rw [hs, wt.property]
  simp

section CentralAction
variable {G : Type} [Group G]

/-- A central element fixing one nonzero vector fixes an irreducible
representation pointwise. This is proved from its actual fixed subspace. -/
theorem central_eq_one_of_fixed (A : Rep k G) (hA : Cohomology.Irreducible A)
    (z : G) (hz : z ∈ Subgroup.center G) (v : A) (hv : v ≠ 0)
    (hfix : A.ρ z v = v) : A.ρ z = 1 := by
  let V : Submodule k A := LinearMap.ker (A.ρ z - 1)
  have hmem (x : A) : x ∈ V ↔ A.ρ z x = x := by
    simp [V, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  have hinv : ∀ g : G, ∀ x : A, x ∈ V → A.ρ g x ∈ V := by
    intro g x hx
    rw [hmem] at hx ⊢
    calc
      A.ρ z (A.ρ g x) = A.ρ (z * g) x := by rw [map_mul, Module.End.mul_apply]
      _ = A.ρ (g * z) x := by rw [Subgroup.mem_center_iff.mp hz g]
      _ = A.ρ g x := by rw [map_mul, Module.End.mul_apply, hx]
  rcases hA.2 V hinv with hbot | htop
  · have hvV : v ∈ V := (hmem v).mpr hfix
    rw [hbot, Submodule.mem_bot] at hvV
    exact (hv hvV).elim
  · apply LinearMap.ext
    intro x
    exact (hmem x).mp (htop ▸ Submodule.mem_top)

/-- Entrywise scalar extension sends the SL center into the SL center. -/
theorem map_center {k' : Type} [Field k'] (f : k →+* k')
    (z : SL n k) (hz : z ∈ Subgroup.center (SL n k)) :
    Matrix.SpecialLinearGroup.map f z ∈ Subgroup.center (SL n k') := by
  obtain ⟨a, ha, heq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨f a, ?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg f ha
  · ext i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => f (M i j)) heq
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite] using h

end CentralAction

/-- Root-lattice central descent follows from the actual torus character
and irreducibility. It is not a special assumption on the desired modules. -/
theorem root_lattice_center_trivial (hn : 0 < n) (wt : Weights.RootLattice n)
    (A : Rep k (SL n k)) (hA : Cohomology.Irreducible A)
    (hw : HasHighestWeight A wt.val) :
    Representation.IsTrivial (A.ρ.comp (Subgroup.center (SL n k)).subtype) := by
  obtain ⟨v, hv, _, htorus⟩ := hw
  constructor
  intro z
  change A.ρ z.val = 1
  apply central_eq_one_of_fixed A hA z.val z.property v hv
  obtain ⟨r, hr, hmatrix⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp z.property
  simp only [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by omega : n ≠ 0)] at hr
    exact zero_ne_one hr
  let a : kˣ := Units.mk0 r hr0
  have ht : ∏ _i : Fin n, a = 1 := by
    apply Units.ext
    simpa [a] using hr
  have heq : torusElement (fun _ : Fin n => a) ht = z.val := by
    apply Subtype.ext
    change Matrix.diagonal (fun _ : Fin n => r) = _
    exact hmatrix
  have h := htorus (fun _ => a) ht
  rw [heq, character_scalar wt a, one_smul] at h
  exact h

/-- Restriction to the prime-field group is an actual restriction functor
along entrywise scalar extension of special-linear matrices. -/
def restrictPrime (n p : ℕ) [Fact p.Prime]
    (A : Rep (Cohomology.PrimeClosure p) (SL n (Cohomology.PrimeClosure p))) :
    Rep (Cohomology.PrimeClosure p) (SL n (ZMod p)) :=
  (Action.res _
    (Matrix.SpecialLinearGroup.map (algebraMap (ZMod p) (Cohomology.PrimeClosure p)))).obj A

theorem restrictPrime_action (n p : ℕ) [Fact p.Prime]
    (A : Rep (Cohomology.PrimeClosure p) (SL n (Cohomology.PrimeClosure p)))
    (g : SL n (ZMod p)) (x : A) :
    (restrictPrime n p A).ρ g x =
      A.ρ (Matrix.SpecialLinearGroup.map
        (algebraMap (ZMod p) (Cohomology.PrimeClosure p)) g) x := rfl

end Guralnick.HighestWeight
