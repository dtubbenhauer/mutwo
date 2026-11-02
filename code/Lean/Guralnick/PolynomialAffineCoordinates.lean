import Guralnick.LatticeCompletionCoordinates
import Guralnick.AffineLatticePosition

/-!
# Polynomial affine coordinate models

The coordinate lattices and affine-window action are defined directly in
k[t,t⁻¹]^N. Their completions are the manuscript's existing completed
coordinate modules, with the same signs of winding and source/target order.
-/
noncomputable section
namespace Guralnick.PolynomialAffineCoordinates
open PolynomialLattice
open scoped BigOperators
variable (k : Type*) [Field k] (N : ℕ)

/-- A signed monomial in the independent Laurent-polynomial ring. -/
def monomial (a : ℤ) : LaurentPolynomial k := LaurentPolynomial.T a

@[simp] theorem monomial_zero : monomial k 0 = 1 := LaurentPolynomial.T_zero

theorem monomial_mul (a b : ℤ) : monomial k a * monomial k b = monomial k (a+b) :=
  (LaurentPolynomial.T_add a b).symm

/-- The same affine window acts on actual Laurent-polynomial vectors. -/
def windowEquiv (w : AffinePermutation N) : Ambient k N ≃ₗ[LaurentPolynomial k] Ambient k N where
  toFun x i := monomial k (-w.winding (w.residue.symm i)) * x (w.residue.symm i)
  invFun x i := monomial k (w.winding i) * x (w.residue i)
  left_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply,← mul_assoc,monomial_mul,add_neg_cancel,
      monomial_zero,one_mul]
  right_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply,← mul_assoc,monomial_mul,neg_add_cancel,
      monomial_zero,one_mul]
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' a x := by
    funext i
    change monomial k _ * (a*x _) = a*(monomial k _ * x _)
    ring

/-- The included window action is literally the completed monomial action. -/
theorem inclusion_window (w : AffinePermutation N) (x : Ambient k N) :
    vectorInclusion k N (windowEquiv k N w x) =
      AffineLatticePosition.windowEquiv k N w (vectorInclusion k N x) := by
  funext i
  change inclusion k (monomial k _ * x _) =
    AffineLatticePosition.monomial k _ * inclusion k (x _)
  rw [map_mul]
  congr 1
  exact inclusion_T k _

/-- The full signed coordinate vector. -/
def coordinateVector (i : Fin N) (q : ℤ) : Ambient k N :=
  Pi.single i (monomial k (-q))

theorem inclusion_coordinateVector (i : Fin N) (q : ℤ) :
    vectorInclusion k N (coordinateVector k N i q) =
      AffineLatticePosition.coordinateVector k N i q :=
  vectorInclusion_monomial k i (-q)

/-- The polynomial coordinate module, before any completion. -/
def coordinateModule (a : ℕ) : Submodule (Polynomial k) (Ambient k N) :=
  Submodule.span (Polynomial k)
    (Set.range fun i : Fin N => coordinateVector k N i (if i.val<a then 1 else 0))

theorem coordinateModule_finite (a : ℕ) : (coordinateModule k N a).FG :=
  Submodule.fg_span (Set.finite_range _)

/-- Polynomial coordinate modules already have full Laurent-polynomial span. -/
theorem coordinateModule_spanning (a : ℕ) :
    Submodule.span (LaurentPolynomial k) (coordinateModule k N a : Set (Ambient k N)) = ⊤ := by
  classical
  apply top_unique
  intro x _
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro i _
  let q : ℤ := if i.val<a then 1 else 0
  have hgen : coordinateVector k N i q ∈ coordinateModule k N a :=
    Submodule.subset_span ⟨i,rfl⟩
  have hspan := Submodule.subset_span (R := LaurentPolynomial k) hgen
  have hmul := (Submodule.span (LaurentPolynomial k)
    (coordinateModule k N a : Set (Ambient k N))).smul_mem (x i * monomial k q) hspan
  have he : (x i * monomial k q) • coordinateVector k N i q = Pi.single i (x i) := by
    funext j
    by_cases h : i = j
    · subst j
      simp only [coordinateVector,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,
        mul_assoc,monomial_mul,add_neg_cancel,monomial_zero,mul_one]
    · simp [coordinateVector,h]
  rwa [he] at hmul

/-- The actual independent polynomial coordinate lattice. -/
def coordinateLattice (a : ℕ) : Lattice k N where
  module := coordinateModule k N a
  finite := coordinateModule_finite k N a
  spanning := coordinateModule_spanning k N a

/-- Completion uses exactly the original manuscript coordinate module. -/
theorem complete_coordinateModule (a : ℕ) :
    LatticeCompletion.completeModule (coordinateModule k N a) =
      AffineLatticePosition.coordinateModule k N a := by
  rw [coordinateModule,LatticeCompletion.complete_span_range]
  simp only [inclusion_coordinateVector,AffineLatticePosition.coordinateModule]

theorem complete_coordinateLattice (a : ℕ) :
    LatticeCompletion.complete (coordinateLattice k N a) =
      AffineLatticePosition.coordinateLattice k N a := by
  apply LaurentLattice.Lattice.ext
  exact complete_coordinateModule k N a

/-- Actual polynomial-linear change of coordinates. -/
def mapModule (g : Ambient k N ≃ₗ[LaurentPolynomial k] Ambient k N)
    (M : Submodule (Polynomial k) (Ambient k N)) : Submodule (Polynomial k) (Ambient k N) :=
  M.map (g.restrictScalars (Polynomial k)).toLinearMap

/-- A Laurent-polynomial change of basis preserves actual full polynomial lattices. -/
def mapLattice (g : Ambient k N ≃ₗ[LaurentPolynomial k] Ambient k N)
    (Λ : Lattice k N) : Lattice k N where
  module := mapModule k N g Λ.module
  finite := Λ.finite.map _
  spanning := by
    change Submodule.span (LaurentPolynomial k)
      (g.toLinearMap '' (Λ.module : Set (Ambient k N))) = ⊤
    rw [← Submodule.map_span,Λ.spanning,Submodule.map_top]
    exact g.range

@[simp] theorem mapLattice_module (g : Ambient k N ≃ₗ[LaurentPolynomial k] Ambient k N)
    (Λ : Lattice k N) : (mapLattice k N g Λ).module = mapModule k N g Λ.module := rfl

/-- Completion commutes with every affine monomial window on every actual
polynomial submodule; this is stronger than matching one numerical matrix. -/
theorem complete_windowModule (w : AffinePermutation N)
    (M : Submodule (Polynomial k) (Ambient k N)) :
    LatticeCompletion.completeModule (mapModule k N (windowEquiv k N w) M) =
      AffineLatticePosition.mapModule k N (AffineLatticePosition.windowEquiv k N w)
        (LatticeCompletion.completeModule M) := by
  unfold LatticeCompletion.completeModule AffineLatticePosition.mapModule
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨vectorInclusion k N z,⟨z,hz,rfl⟩,(inclusion_window k N w z).symm⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨windowEquiv k N w z,⟨z,hz,rfl⟩,inclusion_window k N w z⟩

/-- In particular, both endpoints of a canonical affine-coordinate pair
match their completed counterparts with unchanged window. -/
theorem complete_window_coordinateModule (w : AffinePermutation N) (a : ℕ) :
    LatticeCompletion.completeModule
      (mapModule k N (windowEquiv k N w) (coordinateModule k N a)) =
      AffineLatticePosition.mapModule k N (AffineLatticePosition.windowEquiv k N w)
        (AffineLatticePosition.coordinateModule k N a) := by
  rw [complete_windowModule,complete_coordinateModule]

#print axioms complete_coordinateLattice
#print axioms complete_window_coordinateModule
end Guralnick.PolynomialAffineCoordinates
