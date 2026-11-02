import Guralnick.LatticePeriod
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite relative quotients of actual Laurent lattices

Denominator clearing and finite generation produce a power of t sending
one full lattice into another. Iterating actual one-period expansions and
finite-dimensional quotient extensions proves finiteness of the relative
quotient.
-/
noncomputable section
namespace Guralnick.LaurentLattice
open scoped BigOperators
variable {k : Type*} [Field k] {N : ℕ}

/-- Increasing a denominator-clearing power preserves lattice membership. -/
theorem X_pow_smul_mem_of_le (Λ : Lattice k N) {x : Ambient k N}
    {r s : ℕ} (h : r ≤ s) (hx : (PowerSeries.X : PowerSeries k)^r • x ∈ Λ.module) :
    (PowerSeries.X : PowerSeries k)^s • x ∈ Λ.module := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul]
  exact Λ.module.smul_mem _ hx

/-- A single Laurent scalar has a power-of-t denominator. -/
theorem laurent_clear_denominator (a : LaurentSeries k) :
    ∃ d : ℕ, ∃ f : PowerSeries k,
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^d) * a =
        algebraMap (PowerSeries k) (LaurentSeries k) f := by
  obtain ⟨⟨f,s⟩,h⟩ := IsLocalization.surj
    (Submonoid.powers (PowerSeries.X : PowerSeries k)) a
  obtain ⟨d,hd⟩ := s.property
  refine ⟨d,f,?_⟩
  simpa only [← hd,mul_comm] using h

/-- Fullness supplies a denominator for every actual ambient vector. -/
theorem exists_X_pow_smul_mem (Λ : Lattice k N) (x : Ambient k N) :
    ∃ r : ℕ, (PowerSeries.X : PowerSeries k)^r • x ∈ Λ.module := by
  have hx : x ∈ Submodule.span (LaurentSeries k) (Λ.module : Set (Ambient k N)) := by
    rw [Λ.spanning]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0,by simpa using hy⟩
  | zero => exact ⟨0,by simp⟩
  | add y z hy hz iy iz =>
    obtain ⟨r,hr⟩ := iy
    obtain ⟨s,hs⟩ := iz
    refine ⟨max r s,?_⟩
    rw [smul_add]
    exact Λ.module.add_mem
      (X_pow_smul_mem_of_le Λ (le_max_left r s) hr)
      (X_pow_smul_mem_of_le Λ (le_max_right r s) hs)
  | smul a y hy iy =>
    obtain ⟨r,hr⟩ := iy
    obtain ⟨d,f,hf⟩ := laurent_clear_denominator a
    refine ⟨d+r,?_⟩
    have he : (PowerSeries.X : PowerSeries k)^(d+r) • (a • y) =
        f • ((PowerSeries.X : PowerSeries k)^r • y) := by
      funext i
      change algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^(d+r)) *
        (a * y i) = algebraMap (PowerSeries k) (LaurentSeries k) f *
          (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^r) * y i)
      rw [pow_add,map_mul,← hf]
      ring
    rw [he]
    exact Λ.module.smul_mem f hr

/-- A single power clears the denominators of all elements of a finitely
generated lattice. This is uniform in the two actual lattices. -/
theorem exists_X_pow_smul_le (Λ M : Lattice k N) :
    ∃ r : ℕ, ∀ x ∈ M.module, (PowerSeries.X : PowerSeries k)^r • x ∈ Λ.module := by
  classical
  obtain ⟨d,g,hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp M.finite
  choose r hr using fun i : Fin d => exists_X_pow_smul_mem Λ (g i)
  let b := Finset.univ.sup r
  refine ⟨b,fun x hx => ?_⟩
  rw [← hg] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i,rfl⟩ := hy
    exact X_pow_smul_mem_of_le Λ (Finset.le_sup (Finset.mem_univ i)) (hr i)
  | zero => simp
  | add y z hy hz iy iz => exact by rw [smul_add]; exact Λ.module.add_mem iy iz
  | smul a y hy iy =>
    rw [smul_comm]
    exact Λ.module.smul_mem a iy

/-- Finite-dimensionality is closed under a chain of actual subquotients. -/
theorem quotient_chain_finite {V : Type*} [AddCommGroup V] [Module k V]
    (B C A : Submodule k V) (hBC : B ≤ C) (hCA : C ≤ A)
    [FiniteDimensional k (LatticeGallery.QuotientSpace B C)]
    [FiniteDimensional k (LatticeGallery.QuotientSpace C A)] :
    FiniteDimensional k (LatticeGallery.QuotientSpace B A) := by
  let B' := B.comap A.subtype
  let C' := C.comap A.subtype
  let U := C'.map B'.mkQ
  let e₁ := LatticeGallery.subquotientEquivImage B C A hCA
  let e₂ := Submodule.quotientQuotientEquivQuotient B' C' (Submodule.comap_mono hBC)
  letI : FiniteDimensional k U := Module.Finite.of_surjective e₁.toLinearMap e₁.surjective
  letI : FiniteDimensional k ((LatticeGallery.QuotientSpace B A) ⧸ U) :=
    Module.Finite.of_surjective e₂.symm.toLinearMap e₂.symm.surjective
  exact Module.Finite.of_submodule_quotient U

/-- Iterated expansion is a sequence of actual full lattices. -/
def periodTower (Λ : Lattice k N) : ℕ → Lattice k N
  | 0 => Λ
  | r+1 => intervalLattice (periodTower Λ r)
      (LatticeGallery.expand (shift k N) (periodTower Λ r).space)
      (stable k N (periodTower Λ r)) le_rfl

/-- The r-th actual expanded lattice consists exactly of the vectors whose
r-th t-multiple belongs to the original lattice. -/
theorem mem_periodTower_iff (Λ : Lattice k N) (r : ℕ) (x : Ambient k N) :
    x ∈ (periodTower Λ r).space ↔
      (PowerSeries.X : PowerSeries k)^r • x ∈ Λ.module := by
  induction r generalizing x with
  | zero => simp [periodTower,Lattice.space]
  | succ r ih =>
    change x ∈ LatticeGallery.expand (shift k N) (periodTower Λ r).space ↔ _
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (PowerSeries.X : PowerSeries k)^(r+1) • (shift k N y) ∈ Λ.module
      rw [pow_succ,mul_smul,X_smul_shift]
      exact (ih y).mp hy
    · intro hx
      refine ⟨(PowerSeries.X : PowerSeries k) • x,(ih _).mpr ?_,shift_X_smul x⟩
      simpa only [pow_succ,mul_smul] using hx

theorem le_periodTower (Λ : Lattice k N) (r : ℕ) : Λ.space ≤ (periodTower Λ r).space := by
  intro x hx
  exact (mem_periodTower_iff Λ r x).mpr (Λ.module.smul_mem _ hx)

/-- Period finiteness and explicit denominator bounds imply finite relative
quotients. This lemma does not assume relative-quotient finiteness. -/
theorem finite_quotient_of_period_finite
    (hperiod : ∀ Λ : Lattice k N,
      FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space
        (LatticeGallery.expand (shift k N) Λ.space)))
    (Λ M : Lattice k N) (_hΛM : Λ ≤ M) :
    FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space M.space) := by
  have htower : ∀ r : ℕ,
      FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space (periodTower Λ r).space) := by
    intro r
    induction r with
    | zero =>
      change FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space Λ.space)
      have hz : Λ.space.comap Λ.space.subtype = ⊤ := by ext x; simp
      unfold LatticeGallery.QuotientSpace
      rw [hz]
      letI : Subsingleton (Λ.space ⧸ (⊤ : Submodule k Λ.space)) :=
        (Submodule.Quotient.subsingleton_iff (⊤ : Submodule k Λ.space)).mpr (fun _ => trivial)
      exact Module.Finite.of_surjective
        (0 : k →ₗ[k] (Λ.space ⧸ (⊤ : Submodule k Λ.space)))
        (fun x => ⟨0,Subsingleton.elim _ _⟩)
    | succ r ih =>
      letI : FiniteDimensional k
        (LatticeGallery.QuotientSpace Λ.space (periodTower Λ r).space) := ih
      letI : FiniteDimensional k
        (LatticeGallery.QuotientSpace (periodTower Λ r).space (periodTower Λ (r+1)).space) :=
          hperiod (periodTower Λ r)
      exact quotient_chain_finite Λ.space (periodTower Λ r).space
        (periodTower Λ (r+1)).space (le_periodTower Λ r) (stable k N (periodTower Λ r))
  obtain ⟨r,hr⟩ := exists_X_pow_smul_le Λ M
  have hM : M.space ≤ (periodTower Λ r).space := by
    intro x hx
    exact (mem_periodTower_iff Λ r x).mpr (hr x hx)
  letI : FiniteDimensional k
    (LatticeGallery.QuotientSpace Λ.space (periodTower Λ r).space) := htower r
  let e := LatticeGallery.subquotientEquivImage Λ.space M.space (periodTower Λ r).space hM
  let U := (M.space.comap (periodTower Λ r).space.subtype).map
    (Λ.space.comap (periodTower Λ r).space.subtype).mkQ
  letI : FiniteDimensional k U := FiniteDimensional.finiteDimensional_submodule U
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- Every nested pair of actual full Laurent lattices has a finite-dimensional
relative quotient. No lattice-theory input is used. -/
theorem finite_quotient (Λ M : Lattice k N) (hΛM : Λ ≤ M) :
    FiniteDimensional k (LatticeGallery.QuotientSpace Λ.space M.space) :=
  finite_quotient_of_period_finite period_finite Λ M hΛM

#print axioms finite_quotient
end Guralnick.LaurentLattice
