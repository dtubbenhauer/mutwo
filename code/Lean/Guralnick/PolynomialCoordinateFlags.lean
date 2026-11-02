import Guralnick.PolynomialFlags
import Guralnick.LatticeEquivariance
import Guralnick.OrbitLatticeCuts
import Guralnick.CoordinateLatticeDegree

/-!
# Canonical coordinate flags without a realization assumption

The affine-window action preserves degree because its degree offset is
additive and its Coxeter generators are involutions. Ordered and cyclic
coordinate lattices are checked on their explicit monomial generators.
These facts construct the canonical endpoint flags in the polynomial model.
-/
noncomputable section
namespace Guralnick.PolynomialCoordinateFlags
open LaurentLattice AffineLatticePosition LatticeEquivariance
variable (k : Type) [Field k] (N : ℕ) [NeZero N]

theorem mapLattice_refl (Λ : LaurentLattice.Lattice k N) :
    mapLattice (LinearEquiv.refl (LaurentSeries k) (Ambient k N)) Λ = Λ := by
  apply LaurentLattice.Lattice.ext
  change Λ.module.map (LinearMap.id : Ambient k N →ₗ[PowerSeries k] Ambient k N) = Λ.module
  exact Submodule.map_id _

/-- Every affine Coxeter window preserves the actual signed lattice degree.
The proof uses involutions and additivity, not an assumed winding-degree formula. -/
theorem window_degree (c : Hecke.WindowCoxeter N) (w : AffinePermutation N) :
    ∀ Λ : LaurentLattice.Lattice k N,
      degree k N (mapLattice (windowEquiv k N w) Λ) = degree k N Λ := by
  refine c.system.simple_induction (p := fun u =>
    ∀ Λ : LaurentLattice.Lattice k N, degree k N (mapLattice (windowEquiv k N u) Λ) =
      degree k N Λ) w ?_ ?_ ?_
  · intro s Λ
    let g := windowEquiv k N (c.system.simple s)
    have hgg : mapLattice g (mapLattice g Λ) = Λ := by
      rw [← mapLattice_trans]
      change mapLattice ((windowEquiv k N (c.system.simple s)).trans
        (windowEquiv k N (c.system.simple s))) Λ = Λ
      rw [← windowEquiv_mul,c.system.simple_mul_simple_self,windowEquiv_one,mapLattice_refl]
    have hd := degree_difference g (mapLattice g Λ) Λ
    rw [hgg] at hd
    change degree k N (mapLattice g Λ) = degree k N Λ
    omega
  · intro Λ
    rw [windowEquiv_one,mapLattice_refl]
  · intro u v hu hv Λ
    rw [windowEquiv_mul,mapLattice_trans,hu,hv]

/-- Multiplication by t returns the newly enlarged coordinate to its ordinary level. -/
theorem X_smul_coordinate_one (i : Fin N) :
    (PowerSeries.X : PowerSeries k) • coordinateVector k N i 1 = coordinateVector k N i 0 := by
  have hs : shift k N (coordinateVector k N i 0) = coordinateVector k N i 1 :=
    OrbitMatrix.scalarShift_coordinateVector k N i 0
  rw [← hs]
  exact LaurentLattice.X_smul_shift _

/-- Enlarging the initial coordinate segment enlarges the actual lattice. -/
theorem coordinate_order {a b : ℕ} (hab : a ≤ b) :
    coordinateLattice k N a ≤ coordinateLattice k N b := by
  change coordinateModule k N a ≤ coordinateModule k N b
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  by_cases ha : i.val < a
  · have hb : i.val < b := lt_of_lt_of_le ha hab
    simp only [if_pos ha]
    exact Submodule.subset_span ⟨i,by simp [hb]⟩
  · simp only [if_neg ha]
    by_cases hb : i.val < b
    · rw [← X_smul_coordinate_one k N i]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i,by simp [hb]⟩
    · exact Submodule.subset_span ⟨i,by simp [hb]⟩

/-- Every retained coordinate lattice lies between the standard lattice and its period. -/
theorem coordinate_cyclic (a b : ℕ) (ha : a ≤ N) :
    (coordinateLattice k N a).space ≤
      LatticeGallery.expand (shift k N) (coordinateLattice k N b).space := by
  have hp : (coordinateLattice k N N).space =
      LatticeGallery.expand (shift k N) (coordinateLattice k N 0).space := by
    change (coordinateModule k N N).restrictScalars k = _
    rw [OrbitMatrix.coordinateModule_period]
    rfl
  have h₁ : (coordinateLattice k N a).space ≤ (coordinateLattice k N N).space :=
    coordinate_order k N ha
  have h₂ : (coordinateLattice k N 0).space ≤ (coordinateLattice k N b).space :=
    coordinate_order k N (Nat.zero_le b)
  rw [hp] at h₁
  exact h₁.trans (Submodule.map_mono h₂)

/-- The explicit coordinate flag for an arbitrary retained cyclic mask. -/
def completedTarget (S : Finset (Fin N)) : LatticeFlags.Flag k N S where
  node i := coordinateLattice k N i.val.val
  ordered i j hij := coordinate_order k N hij
  cyclic i j := coordinate_cyclic k N _ _ (Nat.le_of_lt i.val.isLt)
  degree_eq i := coordinateLattice_degree k N i.val.val (Nat.le_of_lt i.val.isLt)

/-- The actual window translate is a normalized completed flag. -/
def completedSource (c : Hecke.WindowCoxeter N) (w : AffinePermutation N)
    (S : Finset (Fin N)) : LatticeFlags.Flag k N S :=
  flagEquiv (windowEquiv k N w) (window_degree k N c w) (completedTarget k N S)

/-- The canonical target flag in the independent polynomial-lattice model. -/
def target (S : Finset (Fin N)) : PolynomialFlags.Flag k N S :=
  PolynomialFlags.algebraizeFlag (completedTarget k N S)

/-- The canonical source flag, with the literal affine winding retained. -/
def source (c : Hecke.WindowCoxeter N) (w : AffinePermutation N)
    (S : Finset (Fin N)) : PolynomialFlags.Flag k N S :=
  PolynomialFlags.algebraizeFlag (completedSource k N c w S)

/-- Algebraization gives the ordinary polynomial coordinate module exactly. -/
theorem target_node_module (S : Finset (Fin N)) (i : {i // i ∈ S}) :
    ((target k N S).node i).module =
      PolynomialAffineCoordinates.coordinateModule k N i.val.val := by
  have he : (target k N S).node i =
      PolynomialAffineCoordinates.coordinateLattice k N i.val.val := by
    apply LatticeCompletion.orderIso.injective
    change LatticeCompletion.complete (LatticeCompletion.algebraize
      (coordinateLattice k N i.val.val)) =
      LatticeCompletion.complete (PolynomialAffineCoordinates.coordinateLattice k N i.val.val)
    rw [LatticeCompletion.complete_algebraize,
      PolynomialAffineCoordinates.complete_coordinateLattice]
  exact congrArg PolynomialLattice.Lattice.module he

/-- The source module is the explicit Laurent-polynomial window translate,
not merely a flag with the expected degree or relative-position label. -/
theorem source_node_module (c : Hecke.WindowCoxeter N) (w : AffinePermutation N)
    (S : Finset (Fin N)) (i : {i // i ∈ S}) :
    ((source k N c w S).node i).module =
      PolynomialAffineCoordinates.mapModule k N (PolynomialAffineCoordinates.windowEquiv k N w)
        (PolynomialAffineCoordinates.coordinateModule k N i.val.val) := by
  let P := PolynomialAffineCoordinates.mapLattice k N
    (PolynomialAffineCoordinates.windowEquiv k N w)
    (PolynomialAffineCoordinates.coordinateLattice k N i.val.val)
  have hP : LatticeCompletion.complete P =
      mapLattice (windowEquiv k N w) (coordinateLattice k N i.val.val) := by
    apply LaurentLattice.Lattice.ext
    exact PolynomialAffineCoordinates.complete_window_coordinateModule k N w i.val.val
  have he : (source k N c w S).node i = P := by
    apply LatticeCompletion.orderIso.injective
    change LatticeCompletion.complete (LatticeCompletion.algebraize
      (mapLattice (windowEquiv k N w) (coordinateLattice k N i.val.val))) =
      LatticeCompletion.complete P
    rw [LatticeCompletion.complete_algebraize,hP]
  exact congrArg PolynomialLattice.Lattice.module he

#print axioms target_node_module
#print axioms source_node_module
#print axioms window_degree
#print axioms coordinate_order
#print axioms coordinate_cyclic
end Guralnick.PolynomialCoordinateFlags
