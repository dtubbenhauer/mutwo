import Guralnick.AffineGroup
import Guralnick.LatticeFlags

/-!
# Affine windows acting on actual Laurent-series coordinates

The periodic index `(i,q)` means `t^(-q)e_i`. Thus the window sends `e_i`
to `t^(-w.winding i)e_(w.residue i)`. This fixes both the seam convention
and the sign of winding. Relative position is an actual simultaneous
coordinate condition on lattice flags: the target is the ordinary
coordinate flag, and the source is its window translate. It has not been
defined by assigning arbitrary affine labels to endpoint pairs.
-/

noncomputable section

namespace Guralnick.AffineLatticePosition

open LaurentLattice LatticeFlags
open Classical
open scoped BigOperators

variable (k : Type*) [Field k] (N : ℕ)

/-- A Laurent monomial in the actual Laurent-series field. -/
def monomial (a : ℤ) : LaurentSeries k := HahnSeries.single a 1

@[simp] theorem monomial_zero : monomial k 0 = 1 := by simp [monomial]

theorem monomial_mul (a b : ℤ) : monomial k a * monomial k b = monomial k (a+b) := by
  simp [monomial, HahnSeries.single_mul_single]

/-- The honest monomial linear equivalence associated to an affine window. -/
def windowEquiv (w : AffinePermutation N) :
    Ambient k N ≃ₗ[LaurentSeries k] Ambient k N where
  toFun x i := monomial k (-w.winding (w.residue.symm i)) * x (w.residue.symm i)
  invFun x i := monomial k (w.winding i) * x (w.residue i)
  left_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply, ← mul_assoc, monomial_mul, add_neg_cancel,
      monomial_zero, one_mul]
  right_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply, ← mul_assoc, monomial_mul, neg_add_cancel,
      monomial_zero, one_mul]
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' a x := by
    funext i
    change monomial k _ * (a*x _) = a*(monomial k _ * x _)
    ring

@[simp] theorem windowEquiv_apply (w : AffinePermutation N) (x : Ambient k N) (i : Fin N) :
    windowEquiv k N w x i =
      monomial k (-w.winding (w.residue.symm i)) * x (w.residue.symm i) := rfl

@[simp] theorem windowEquiv_one : windowEquiv k N 1 = LinearEquiv.refl _ _ := by
  apply LinearEquiv.ext
  intro x
  funext i
  simp [windowEquiv]

/-- Composition of the actual coordinate actions agrees with affine
permutation composition, with the right-hand factor acting first. -/
theorem windowEquiv_mul (u v : AffinePermutation N) :
    windowEquiv k N (u*v) = (windowEquiv k N v).trans (windowEquiv k N u) := by
  apply LinearEquiv.ext
  intro x
  funext i
  change monomial k (-(v.winding (v.residue.symm (u.residue.symm i)) +
      u.winding (v.residue (v.residue.symm (u.residue.symm i))))) *
      x (v.residue.symm (u.residue.symm i)) =
    monomial k (-u.winding (u.residue.symm i)) *
      (monomial k (-v.winding (v.residue.symm (u.residue.symm i))) *
        x (v.residue.symm (u.residue.symm i)))
  rw [Equiv.apply_symm_apply, ← mul_assoc, monomial_mul]
  congr 2
  omega

/-- A coordinate vector with its full periodic integer information. -/
def coordinateVector (i : Fin N) (q : ℤ) : Ambient k N :=
  Pi.single i (monomial k (-q))

theorem windowEquiv_coordinateVector (w : AffinePermutation N) (i : Fin N) (q : ℤ) :
    windowEquiv k N w (coordinateVector k N i q) =
      coordinateVector k N (w.residue i) (q+w.winding i) := by
  funext j
  by_cases hj : j = w.residue i
  · subst j
    simp only [windowEquiv_apply, Equiv.symm_apply_apply, coordinateVector, Pi.single_eq_same]
    rw [Equiv.symm_apply_apply, Pi.single_eq_same, monomial_mul]
    congr 1
    omega
  · have hji : w.residue.symm j ≠ i := by
      intro h
      apply hj
      rw [← h, Equiv.apply_symm_apply]
    simp [windowEquiv_apply, coordinateVector, hj, hji]

/-- The ordinary type-a coordinate lattice module, for a retained position
`a ∈ {0,...,N-1}`: the first a basis directions are enlarged by t^-1. -/
def coordinateModule (a : ℕ) : Submodule (PowerSeries k) (Ambient k N) :=
  Submodule.span (PowerSeries k)
    (Set.range (fun i : Fin N => coordinateVector k N i (if i.val < a then 1 else 0)))

theorem coordinateModule_finite (a : ℕ) : (coordinateModule k N a).FG :=
  Submodule.fg_span (Set.finite_range _)

/-- The explicit coordinate module spans all of k((t))^N, so it is a full
lattice, rather than merely a selected stable subspace. -/
theorem coordinateModule_spanning (a : ℕ) :
    Submodule.span (LaurentSeries k)
      (coordinateModule k N a : Set (Ambient k N)) = ⊤ := by
  apply top_unique
  intro x _
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro i _
  let q : ℤ := if i.val < a then 1 else 0
  have hgen : coordinateVector k N i q ∈ coordinateModule k N a :=
    Submodule.subset_span ⟨i,rfl⟩
  have hspan := Submodule.subset_span (R := LaurentSeries k) hgen
  have hmul := (Submodule.span (LaurentSeries k)
    (coordinateModule k N a : Set (Ambient k N))).smul_mem
      (x i * monomial k q) hspan
  have he : (x i * monomial k q) • coordinateVector k N i q = Pi.single i (x i) := by
    funext j
    by_cases h : i = j
    · subst j
      simp only [coordinateVector, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_assoc, monomial_mul, add_neg_cancel, monomial_zero, mul_one]
    · simp [coordinateVector, h]
  rwa [he] at hmul

def coordinateLattice (a : ℕ) : Lattice k N where
  module := coordinateModule k N a
  finite := coordinateModule_finite k N a
  spanning := coordinateModule_spanning k N a

/-- Type zero is exactly the standard power-series lattice used to define
the signed relative degree in `LaurentLattice`. -/
theorem coordinateModule_zero : coordinateModule k N 0 = standardModule k N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    funext j
    by_cases h : i = j
    · subst j
      simp [standardEmbedding, coordinateVector]
    · simp [standardEmbedding, coordinateVector, h]
  · rintro x ⟨f,rfl⟩
    rw [← Finset.univ_sum_single f, map_sum]
    apply Submodule.sum_mem
    intro i _
    have he : standardEmbedding k N (Pi.single i (f i)) =
        (f i) • coordinateVector k N i 0 := by
      funext j
      by_cases h : i = j
      · subst j
        simp [standardEmbedding, coordinateVector, Algebra.smul_def]
      · simp [standardEmbedding, coordinateVector, h]
    rw [he]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, by simp⟩

/-- Map a lattice module by the actual Laurent-linear coordinate change. -/
def mapModule (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (S : Submodule (PowerSeries k) (Ambient k N)) :
    Submodule (PowerSeries k) (Ambient k N) :=
  S.map (g.restrictScalars (PowerSeries k)).toLinearMap

theorem mapModule_trans (e g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (S : Submodule (PowerSeries k) (Ambient k N)) :
    mapModule k N (e.trans g) S = mapModule k N g (mapModule k N e S) := by
  unfold mapModule
  rw [← Submodule.map_comp]
  rfl

/-- Every finite residue permutation preserves the type-zero lattice.
This is proved from its action on the actual generating coordinate vectors. -/
theorem window_preserves_zero (w : AffinePermutation N) (hw : ∀ i, w.winding i = 0) :
    mapModule k N (windowEquiv k N w) (coordinateModule k N 0) = coordinateModule k N 0 := by
  unfold mapModule coordinateModule
  simp only [Nat.not_lt_zero, if_false]
  rw [Submodule.map_span, ← Set.range_comp']
  have he : (fun i : Fin N =>
      ((windowEquiv k N w).restrictScalars (PowerSeries k)).toLinearMap (coordinateVector k N i 0)) =
      (fun i : Fin N => coordinateVector k N (w.residue i) 0) := by
    funext i
    change windowEquiv k N w (coordinateVector k N i 0) = _
    rw [windowEquiv_coordinateVector, hw, zero_add]
  rw [he]
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨w.residue i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨w.residue.symm i,by simp⟩

/-- The literal target/source convention for the left-output/right-source
Hecke corner. A single ambient basis identifies the target with ordinary
coordinate modules and the source with their affine-window translates. -/
def RelativePosition {S T : Finset (Fin N)}
    (target : Flag k N T) (source : Flag k N S) (w : AffinePermutation N) : Prop :=
  ∃ g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N,
    (∀ i, mapModule k N g (coordinateModule k N i.val.val) = (target.node i).module) ∧
    (∀ i, mapModule k N ((windowEquiv k N w).trans g)
      (coordinateModule k N i.val.val) = (source.node i).module)

/-- Relative position one forces agreement of the common retained lattices. -/
theorem relativePosition_one_compatible {S T : Finset (Fin N)}
    {target : Flag k N T} {source : Flag k N S}
    (h : RelativePosition k N target source 1) : Compatible target source := by
  obtain ⟨g,ht,hs⟩ := h
  intro i hi hj
  apply LaurentLattice.Lattice.ext
  rw [← ht ⟨i,hi⟩, ← hs ⟨i,hj⟩, windowEquiv_one]
  rfl

/-- A zero-winding position identifies the actual type-zero endpoint
lattices whenever both boundaries retain that vertex. -/
theorem relativePosition_zero_nodes_eq [NeZero N] {S T : Finset (Fin N)}
    {target : Flag k N T} {source : Flag k N S} {w : AffinePermutation N}
    (h : RelativePosition k N target source w) (hw : ∀ i, w.winding i = 0)
    (hT : (0 : Fin N) ∈ T) (hS : (0 : Fin N) ∈ S) :
    target.node ⟨0,hT⟩ = source.node ⟨0,hS⟩ := by
  obtain ⟨g,ht,hs⟩ := h
  apply LaurentLattice.Lattice.ext
  rw [← ht ⟨0,hT⟩, ← hs ⟨0,hS⟩]
  simp only [Fin.val_zero, mapModule_trans, window_preserves_zero k N w hw]

/-- The ordinary finite longest element has the same spherical source
vertex as the identity. Its permutation of the packet is retained. -/
theorem relativePosition_longest_zero_nodes_eq [NeZero N] {S T : Finset (Fin N)}
    {target : Flag k N T} {source : Flag k N S}
    (h : RelativePosition k N target source (AffinePermutation.longest N))
    (hT : (0 : Fin N) ∈ T) (hS : (0 : Fin N) ∈ S) :
    target.node ⟨0,hT⟩ = source.node ⟨0,hS⟩ :=
  relativePosition_zero_nodes_eq k N h (by simp) hT hS

end Guralnick.AffineLatticePosition
