import Guralnick.LatticeCompletionDimensions

/-!
# The affine parameter and completion

The polynomial shift is multiplication by the actual Laurent monomial
 t⁻¹. The natural ambient inclusion intertwines it with the completed
shift, and completion preserves the cyclic containment used in affine flags.
-/
noncomputable section
namespace Guralnick.PolynomialLattice
variable (k : Type*) [Field k] (N : ℕ)

theorem negPower_X_pow (r : ℕ) (x : Ambient k N) :
    negPower k N r ((Polynomial.X : Polynomial k)^r • x) = x := by
  apply X_pow_smul_injective k N r
  change (Polynomial.X : Polynomial k)^r • negPower k N r
      ((Polynomial.X : Polynomial k)^r • x) = (Polynomial.X : Polynomial k)^r • x
  rw [X_pow_negPower]

/-- Actual multiplication by t⁻¹ on Laurent-polynomial vectors. -/
def shift : Ambient k N ≃ₗ[k] Ambient k N where
  toFun := negPower k N 1
  invFun := fun x => (Polynomial.X : Polynomial k) • x
  left_inv := fun x => by simpa only [pow_one] using X_pow_negPower k N 1 x
  right_inv := fun x => by simpa only [pow_one] using negPower_X_pow k N 1 x
  map_add' x y := smul_add _ _ _
  map_smul' a x := smul_comm _ _ _

@[simp] theorem X_smul_shift (x : Ambient k N) :
    (Polynomial.X : Polynomial k) • shift k N x = x := by
  exact (shift k N).left_inv x

@[simp] theorem shift_X_smul (x : Ambient k N) :
    shift k N ((Polynomial.X : Polynomial k) • x) = x := by
  exact (shift k N).right_inv x

/-- The diagram of actual ambient shift maps commutes. -/
theorem vectorInclusion_shift (x : Ambient k N) :
    vectorInclusion k N (shift k N x) = LaurentLattice.shift k N (vectorInclusion k N x) := by
  apply series_X_pow_smul_injective k N 1
  simp only [pow_one]
  have h := vectorInclusion_X_pow k N 1 (shift k N x)
  simp only [pow_one,X_smul_shift] at h
  rw [← h,LaurentLattice.X_smul_shift]

/-- Membership in the expanded polynomial subspace is detected by multiplying by t. -/
theorem mem_expand_iff (Λ : Lattice k N) (x : Ambient k N) :
    x ∈ LatticeGallery.expand (shift k N) Λ.space ↔
      (Polynomial.X : Polynomial k) • x ∈ Λ.module := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (Polynomial.X : Polynomial k) • shift k N y ∈ Λ.module
    rwa [X_smul_shift]
  · intro hx
    exact ⟨Polynomial.X • x,hx,shift_X_smul k N x⟩

end Guralnick.PolynomialLattice

namespace Guralnick.LatticeCompletion
variable {k : Type*} [Field k] {N : ℕ}

theorem series_mem_expand_iff (Λ : LaurentLattice.Lattice k N) (x : LaurentLattice.Ambient k N) :
    x ∈ LatticeGallery.expand (LaurentLattice.shift k N) Λ.space ↔
      (PowerSeries.X : PowerSeries k) • x ∈ Λ.module := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (PowerSeries.X : PowerSeries k) • LaurentLattice.shift k N y ∈ Λ.module
    rwa [LaurentLattice.X_smul_shift]
  · intro hx
    exact ⟨PowerSeries.X • x,hx,LaurentLattice.shift_X_smul x⟩

/-- Completion preserves and reflects the periodic containment of actual
lattice pairs. Together with the order isomorphism this transports arbitrary
cyclic flags, including the absolute-degree condition. -/
theorem complete_cyclic_iff (Λ M : PolynomialLattice.Lattice k N) :
    (complete Λ).space ≤ LatticeGallery.expand (LaurentLattice.shift k N) (complete M).space ↔
      Λ.space ≤ LatticeGallery.expand (PolynomialLattice.shift k N) M.space := by
  constructor
  · intro h x hx
    apply (PolynomialLattice.mem_expand_iff k N M x).mpr
    apply (complete_mem_iff M _).mp
    have hh := (series_mem_expand_iff (complete M) _).mp (h (mem_completeModule hx))
    simpa only [PolynomialLattice.vectorInclusion_polynomial_smul,Polynomial.coe_X] using hh
  · intro h x hx
    apply (series_mem_expand_iff (complete M) x).mpr
    change x ∈ completeModule Λ.module at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y,hy,rfl⟩ := hx
      have hh := mem_completeModule ((PolynomialLattice.mem_expand_iff k N M y).mp (h hy))
      simpa only [PolynomialLattice.vectorInclusion_polynomial_smul,Polynomial.coe_X] using hh
    | zero => simp
    | add x y hx hy ihx ihy => rw [smul_add]; exact (complete M).module.add_mem ihx ihy
    | smul a x hx ih => rw [smul_comm]; exact (complete M).module.smul_mem a ih

#print axioms PolynomialLattice.vectorInclusion_shift
#print axioms complete_cyclic_iff
end Guralnick.LatticeCompletion
