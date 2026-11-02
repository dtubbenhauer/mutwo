import Guralnick.LatticeQuotientFinite

/-!
# Actual lattices in a bounded interval

A k-subspace between Λ and t⁻ᵈΛ is a full power-series lattice exactly when
it is stable under t. Truncating an arbitrary power series proves full
power-series stability; the tail lands in Λ. This constructs actual lattices
from bounded ambient subspaces. Their identification with finite quotient
inverse images, and a global comparison of polynomial and completed affine
flags, remain separate steps.
-/
noncomputable section
namespace Guralnick.LaurentLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- Stability under the actual Laurent action of the power-series parameter. -/
def XStable (A : Submodule k (Ambient k N)) : Prop :=
  ∀ x ∈ A, (PowerSeries.X : PowerSeries k) • x ∈ A

/-- An actual power-series lattice is stable under its parameter. -/
theorem lattice_XStable (Λ : Lattice k N) : XStable Λ.space :=
  fun _ hx => Λ.module.smul_mem _ hx

/-- Parameter stability iterates through every nonnegative power. -/
theorem XStable.pow_smul_mem {A : Submodule k (Ambient k N)} (hA : XStable A)
    (r : ℕ) {x : Ambient k N} (hx : x ∈ A) :
    (PowerSeries.X : PowerSeries k)^r • x ∈ A := by
  induction r with
  | zero => simpa using hx
  | succ r ih =>
    rw [pow_succ',mul_smul]
    exact hA _ ih

/-- Parameter stability and k-linearity give stability under polynomial action. -/
theorem XStable.polynomial_smul_mem {A : Submodule k (Ambient k N)} (hA : XStable A)
    (p : Polynomial k) {x : Ambient k N} (hx : x ∈ A) :
    (p : PowerSeries k) • x ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.coe_add,add_smul]
    exact A.add_mem hp hq
  | monomial r a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.coe_mul,Polynomial.coe_C,
      Polynomial.coe_pow,Polynomial.coe_X,mul_smul,C_smul_eq]
    exact A.smul_mem a (hA.pow_smul_mem r hx)

/-- The tail of a power series sends A into Λ, while its finite truncation
preserves A. Thus the actual k-subspace is a power-series submodule. -/
theorem truncated_smul_mem (Λ : Lattice k N) (d : ℕ)
    (A : Submodule k (Ambient k N)) (hlower : Λ.space ≤ A)
    (hupper : A ≤ (periodTower Λ d).space) (hstable : XStable A)
    (f : PowerSeries k) {x : Ambient k N} (hx : x ∈ A) : f • x ∈ A := by
  rw [PowerSeries.eq_shift_mul_X_pow_add_trunc d f,add_smul,mul_smul]
  exact A.add_mem
    (hlower (Λ.module.smul_mem _ ((mem_periodTower_iff Λ d x).mp (hupper hx))))
    (hstable.polynomial_smul_mem _ hx)

/-- The actual power-series submodule with the supplied underlying k-subspace. -/
def truncatedModule (Λ : Lattice k N) (d : ℕ) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A) (hupper : A ≤ (periodTower Λ d).space)
    (hstable : XStable A) : Submodule (PowerSeries k) (Ambient k N) where
  carrier := A
  zero_mem' := A.zero_mem
  add_mem' := A.add_mem
  smul_mem' := truncated_smul_mem Λ d A hlower hupper hstable

/-- Inclusion in the actual upper lattice gives finite generation by
Noetherianity; no quotient-dimension assumption is used. -/
theorem truncatedModule_finite (Λ : Lattice k N) (d : ℕ)
    (A : Submodule k (Ambient k N)) (hlower : Λ.space ≤ A)
    (hupper : A ≤ (periodTower Λ d).space) (hstable : XStable A) :
    (truncatedModule Λ d A hlower hupper hstable).FG := by
  letI : IsNoetherian (PowerSeries k) (periodTower Λ d).module :=
    isNoetherian_of_fg_of_noetherian _ (periodTower Λ d).finite
  let f : truncatedModule Λ d A hlower hupper hstable →ₗ[PowerSeries k]
      (periodTower Λ d).module := Submodule.inclusion hupper
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : (periodTower Λ d).module => z.val) h
  letI : Module.Finite (PowerSeries k) (truncatedModule Λ d A hlower hupper hstable) :=
    Module.Finite.of_injective f hf
  exact Module.Finite.iff_fg.mp inferInstance

/-- Containment of the original full lattice proves full Laurent span. -/
theorem truncatedModule_spanning (Λ : Lattice k N) (d : ℕ)
    (A : Submodule k (Ambient k N)) (hlower : Λ.space ≤ A)
    (hupper : A ≤ (periodTower Λ d).space) (hstable : XStable A) :
    Submodule.span (LaurentSeries k)
      (truncatedModule Λ d A hlower hupper hstable : Set (Ambient k N)) = ⊤ := by
  apply top_unique
  rw [← Λ.spanning]
  exact Submodule.span_mono hlower

/-- The actual full lattice associated to a bounded parameter-stable subspace. -/
def truncatedLattice (Λ : Lattice k N) (d : ℕ) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A) (hupper : A ≤ (periodTower Λ d).space)
    (hstable : XStable A) : Lattice k N where
  module := truncatedModule Λ d A hlower hupper hstable
  finite := truncatedModule_finite Λ d A hlower hupper hstable
  spanning := truncatedModule_spanning Λ d A hlower hupper hstable

@[simp] theorem truncatedLattice_space (Λ : Lattice k N) (d : ℕ)
    (A : Submodule k (Ambient k N)) (hlower : Λ.space ≤ A)
    (hupper : A ≤ (periodTower Λ d).space) (hstable : XStable A) :
    (truncatedLattice Λ d A hlower hupper hstable).space = A := rfl

/-- Within an actual bounded interval, parameter stability is exactly the
condition for being the underlying subspace of a full lattice. -/
theorem XStable_iff_lattice (Λ : Lattice k N) (d : ℕ)
    (A : Submodule k (Ambient k N)) (hlower : Λ.space ≤ A)
    (hupper : A ≤ (periodTower Λ d).space) :
    XStable A ↔ ∃ M : Lattice k N, M.space = A := by
  constructor
  · intro hA
    exact ⟨truncatedLattice Λ d A hlower hupper hA,rfl⟩
  · rintro ⟨M,rfl⟩
    exact lattice_XStable M

/-- Exact inclusion-preserving correspondence between actual full lattices
in the interval and parameter-stable k-subspaces of that interval. -/
def truncatedIntervalIso (Λ : Lattice k N) (d : ℕ) :
    {M : Lattice k N // Λ ≤ M ∧ M ≤ periodTower Λ d} ≃o
      {A : Submodule k (Ambient k N) //
        Λ.space ≤ A ∧ A ≤ (periodTower Λ d).space ∧ XStable A} where
  toFun M := ⟨M.val.space,M.property.1,M.property.2,lattice_XStable M.val⟩
  invFun A := ⟨truncatedLattice Λ d A.val A.property.1 A.property.2.1 A.property.2.2,
    A.property.1,A.property.2.1⟩
  left_inv M := by
    apply Subtype.ext
    apply Lattice.ext
    ext x
    rfl
  right_inv A := by apply Subtype.ext; rfl
  map_rel_iff' := Iff.rfl

/-- At d=0 both bounds force the original lattice. -/
theorem truncatedLattice_zero (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A) (hupper : A ≤ (periodTower Λ 0).space)
    (hstable : XStable A) : truncatedLattice Λ 0 A hlower hupper hstable = Λ := by
  apply Lattice.ext
  ext x
  change x ∈ A ↔ x ∈ Λ.space
  exact ⟨fun hx => hupper hx, fun hx => hlower hx⟩

/-- In a one-period interval, parameter stability is automatic. -/
theorem one_period_XStable (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A) (hupper : A ≤ (periodTower Λ 1).space) : XStable A := by
  intro x hx
  apply hlower
  simpa only [pow_one] using (mem_periodTower_iff Λ 1 x).mp (hupper hx)

/-- The new construction agrees with the previous one-period lattice lift. -/
theorem truncatedLattice_one (Λ : Lattice k N) (A : Submodule k (Ambient k N))
    (hlower : Λ.space ≤ A) (hupper : A ≤ (periodTower Λ 1).space) :
    truncatedLattice Λ 1 A hlower hupper (one_period_XStable Λ A hlower hupper) =
      intervalLattice Λ A hlower hupper := by
  apply Lattice.ext
  ext x
  rfl

#print axioms XStable_iff_lattice
#print axioms truncatedIntervalIso
#print axioms truncatedLattice_zero
#print axioms truncatedLattice_one
end Guralnick.LaurentLattice
