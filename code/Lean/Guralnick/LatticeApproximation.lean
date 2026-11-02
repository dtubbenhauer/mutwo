import Guralnick.LatticeCompletion

/-!
# Finite Laurent-polynomial approximation

A Laurent-series vector can be represented modulo any standard positive
power of t by an actual Laurent-polynomial vector. Within the completion
of a polynomial lattice the representative can be chosen in that lattice.
These are finite truncation arguments, not topological density assumptions.
-/
noncomputable section
namespace Guralnick.LatticeCompletion
variable {k : Type*} [Field k] {N : ℕ}

/-- Every actual Laurent vector has an actual polynomial representative
modulo the indicated standard t-power. -/
theorem approximate (x : LaurentLattice.Ambient k N) (r : ℕ) :
    ∃ y : PolynomialLattice.Ambient k N,
      x - PolynomialLattice.vectorInclusion k N y ∈ seriesSmall (k := k) (N := N) r := by
  obtain ⟨s,hs⟩ := LaurentLattice.exists_X_pow_smul_mem (LaurentLattice.standardLattice k N) x
  obtain ⟨f,hf⟩ := hs
  let p : Fin N → Polynomial k := fun i => PowerSeries.trunc (r+s) (f i)
  let g : Fin N → PowerSeries k := fun i => PowerSeries.mk
    (fun n => PowerSeries.coeff k (n+(r+s)) (f i))
  let y := PolynomialLattice.negPower k N s (PolynomialLattice.standardEmbedding k N p)
  refine ⟨y,LaurentLattice.standardEmbedding k N g,⟨g,rfl⟩,?_⟩
  change (PowerSeries.X : PowerSeries k)^r • LaurentLattice.standardEmbedding k N g =
    x - PolynomialLattice.vectorInclusion k N y
  apply PolynomialLattice.series_X_pow_smul_injective k N s
  change (PowerSeries.X : PowerSeries k)^s •
      ((PowerSeries.X : PowerSeries k)^r • LaurentLattice.standardEmbedding k N g) =
    (PowerSeries.X : PowerSeries k)^s • (x - PolynomialLattice.vectorInclusion k N y)
  rw [smul_sub,← PolynomialLattice.vectorInclusion_X_pow,
    PolynomialLattice.X_pow_negPower,← hf,PolynomialLattice.vectorInclusion_standard]
  apply eq_sub_iff_add_eq.mpr
  funext i
  change algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^s) *
      (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^r) *
        algebraMap (PowerSeries k) (LaurentSeries k) (g i)) +
      algebraMap (PowerSeries k) (LaurentSeries k) (p i : PowerSeries k) =
    algebraMap (PowerSeries k) (LaurentSeries k) (f i)
  rw [← mul_assoc,← map_mul,← map_mul,← map_add]
  congr 1
  have h := PowerSeries.eq_shift_mul_X_pow_add_trunc (r+s) (f i)
  change PowerSeries.X^s * PowerSeries.X^r * g i + (p i : PowerSeries k) = f i
  rw [← pow_add,Nat.add_comm s r,mul_comm (PowerSeries.X^(r+s))]
  exact h.symm

/-- A coefficient can be truncated without changing the lattice vector
modulo a prescribed lower standard power. -/
theorem smul_approximation (r s : ℕ) (a : PowerSeries k)
    (y : PolynomialLattice.Ambient k N)
    (hy : (Polynomial.X : Polynomial k)^s • y ∈ PolynomialLattice.standardModule k N) :
    a • PolynomialLattice.vectorInclusion k N y -
      PolynomialLattice.vectorInclusion k N (PowerSeries.trunc (r+s) a • y) ∈
        seriesSmall (k := k) (N := N) r := by
  let g : PowerSeries k := PowerSeries.mk
    (fun n => PowerSeries.coeff k (n+(r+s)) a)
  have hs : (PowerSeries.X : PowerSeries k)^s • PolynomialLattice.vectorInclusion k N y ∈
      LaurentLattice.standardModule k N := by
    rw [← PolynomialLattice.vectorInclusion_X_pow]
    exact (PolynomialLattice.vectorInclusion_mem_standard_iff k N _).mpr hy
  refine ⟨g • ((PowerSeries.X : PowerSeries k)^s • PolynomialLattice.vectorInclusion k N y),
    (LaurentLattice.standardModule k N).smul_mem g hs,?_⟩
  change (PowerSeries.X : PowerSeries k)^r •
      (g • ((PowerSeries.X : PowerSeries k)^s • PolynomialLattice.vectorInclusion k N y)) = _
  rw [PolynomialLattice.vectorInclusion_polynomial_smul]
  apply eq_sub_iff_add_eq.mpr
  rw [smul_smul,smul_smul,← add_smul]
  congr 1
  calc
    PowerSeries.X^r * g * PowerSeries.X^s + (PowerSeries.trunc (r+s) a : PowerSeries k) =
        g * PowerSeries.X^(r+s) + (PowerSeries.trunc (r+s) a : PowerSeries k) := by
      rw [pow_add]; ring
    _ = a := (PowerSeries.eq_shift_mul_X_pow_add_trunc (r+s) a).symm

/-- Representatives can be chosen in the original polynomial submodule;
there is no assumption that elementary diagrams or numerical matrices
already represent completed lattices. -/
theorem approximate_in_complete
    (M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N)) (s : ℕ)
    (hs : ∀ y ∈ M, (Polynomial.X : Polynomial k)^s • y ∈ PolynomialLattice.standardModule k N)
    (r : ℕ) {x : LaurentLattice.Ambient k N} (hx : x ∈ completeModule M) :
    ∃ y ∈ M, x - PolynomialLattice.vectorInclusion k N y ∈ seriesSmall (k := k) (N := N) r := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,hy,by simp⟩
  | zero => exact ⟨0,M.zero_mem,by simp⟩
  | add x z hx hz ihx ihz =>
    obtain ⟨y,hy,hey⟩ := ihx
    obtain ⟨w,hw,hew⟩ := ihz
    refine ⟨y+w,M.add_mem hy hw,?_⟩
    rw [map_add,show x+z-(PolynomialLattice.vectorInclusion k N y+
      PolynomialLattice.vectorInclusion k N w) =
        (x-PolynomialLattice.vectorInclusion k N y)+(z-PolynomialLattice.vectorInclusion k N w)
      from by abel]
    exact (seriesSmall r).add_mem hey hew
  | smul a x hx ih =>
    obtain ⟨y,hy,hey⟩ := ih
    refine ⟨PowerSeries.trunc (r+s) a • y,M.smul_mem _ hy,?_⟩
    have he : a • x - PolynomialLattice.vectorInclusion k N (PowerSeries.trunc (r+s) a • y) =
        a • (x-PolynomialLattice.vectorInclusion k N y) +
        (a • PolynomialLattice.vectorInclusion k N y -
          PolynomialLattice.vectorInclusion k N (PowerSeries.trunc (r+s) a • y)) := by
      rw [smul_sub]; abel
    rw [he]
    exact (seriesSmall r).add_mem ((seriesSmall r).smul_mem a hey)
      (smul_approximation r s a y (hs y hy))

/-- Algebraizing the completion recovers the actual original polynomial lattice. -/
theorem algebraize_complete (Λ : PolynomialLattice.Lattice k N) :
    algebraize (complete Λ) = Λ := by
  apply PolynomialLattice.Lattice.ext
  apply le_antisymm
  · intro x hx
    obtain ⟨r,hr⟩ := polynomial_lower_bound Λ
    obtain ⟨s,hs⟩ := PolynomialLattice.exists_X_pow_smul_le k N
      (PolynomialLattice.standardLattice k N) Λ
    obtain ⟨y,hy,he⟩ := approximate_in_complete Λ.module s hs r hx
    have hd : x-y ∈ polynomialSmall r := by
      rw [← algebraize_small]
      change PolynomialLattice.vectorInclusion k N (x-y) ∈ seriesSmall r
      simpa only [map_sub] using he
    have := Λ.module.add_mem (hr hd) hy
    simpa only [sub_add_cancel] using this
  · intro x hx
    exact mem_completeModule hx

/-- Completion of the actual inverse image recovers every completed lattice. -/
theorem complete_algebraize (Λ : LaurentLattice.Lattice k N) :
    complete (algebraize Λ) = Λ := by
  apply LaurentLattice.Lattice.ext
  apply le_antisymm
  · exact (complete_le_iff _ _).mpr le_rfl
  · intro x hx
    obtain ⟨r,hr⟩ := series_lower_bound Λ
    obtain ⟨y,hy⟩ := approximate x r
    have hym : y ∈ (algebraize Λ).module := by
      change PolynomialLattice.vectorInclusion k N y ∈ Λ.module
      have := Λ.module.sub_mem hx (hr hy)
      simpa only [sub_sub_cancel] using this
    have hs : seriesSmall (k := k) (N := N) r ≤ completeModule (algebraize Λ).module := by
      apply small_le_complete
      rw [← algebraize_small]
      exact algebraizeModule_mono hr
    have := (completeModule (algebraize Λ).module).add_mem (hs hy) (mem_completeModule hym)
    simpa only [sub_add_cancel] using this

/-- The full, natural order equivalence between the two independent actual models. -/
def orderIso : PolynomialLattice.Lattice k N ≃o LaurentLattice.Lattice k N where
  toFun := complete
  invFun := algebraize
  left_inv := algebraize_complete
  right_inv := complete_algebraize
  map_rel_iff' := by
    intro Λ M
    constructor
    · intro h
      have hh := algebraizeModule_mono h
      change (algebraize (complete Λ)).module ≤ (algebraize (complete M)).module at hh
      simpa only [algebraize_complete] using hh
    · intro h; exact completeModule_mono (k := k) (N := N) h

@[simp] theorem complete_mem_iff (Λ : PolynomialLattice.Lattice k N)
    (x : PolynomialLattice.Ambient k N) :
    PolynomialLattice.vectorInclusion k N x ∈ (complete Λ).module ↔ x ∈ Λ.module := by
  change x ∈ (algebraize (complete Λ)).module ↔ _
  rw [algebraize_complete]

@[simp] theorem complete_standardLattice :
    complete (PolynomialLattice.standardLattice k N) = LaurentLattice.standardLattice k N := by
  apply LaurentLattice.Lattice.ext
  exact complete_standard

#print axioms orderIso
end Guralnick.LatticeCompletion
