import Guralnick.PolynomialLattice
import Guralnick.LatticeDegree
import Guralnick.LatticeTruncatedLift

/-!
# Completion and algebraization of actual full lattices

Completion takes the power-series span of the natural Laurent-polynomial
image. Algebraization takes its inverse image. Both maps are defined on
actual submodules; the inverse identities are consequences of denominator
bounds and finite truncation.
-/
noncomputable section
namespace Guralnick.LatticeCompletion
open PolynomialLattice
variable {k : Type*} [Field k] {N : ℕ}

instance polynomialSeriesTower :
    IsScalarTower (Polynomial k) (PowerSeries k) (LaurentSeries k) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Extension of scalars, realized as an actual ambient span. -/
def completeModule (M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N)) :
    Submodule (PowerSeries k) (LaurentLattice.Ambient k N) :=
  Submodule.span (PowerSeries k) (PolynomialLattice.vectorInclusion k N '' (M : Set _))

/-- Inverse image under the fixed coefficientwise inclusion. -/
def algebraizeModule (M : Submodule (PowerSeries k) (LaurentLattice.Ambient k N)) :
    Submodule (Polynomial k) (PolynomialLattice.Ambient k N) :=
  (M.restrictScalars (Polynomial k)).comap (PolynomialLattice.vectorInclusion k N)

@[simp] theorem mem_algebraizeModule (M : Submodule (PowerSeries k) (LaurentLattice.Ambient k N))
    (x : PolynomialLattice.Ambient k N) :
    x ∈ algebraizeModule M ↔ PolynomialLattice.vectorInclusion k N x ∈ M := Iff.rfl

theorem completeModule_mono : Monotone (completeModule (k := k) (N := N)) := by
  intro M L h
  exact Submodule.span_mono (Set.image_mono h)

theorem algebraizeModule_mono : Monotone (algebraizeModule (k := k) (N := N)) := by
  intro M L h x hx
  exact h hx

theorem mem_completeModule {M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N)}
    {x : PolynomialLattice.Ambient k N} (hx : x ∈ M) :
    PolynomialLattice.vectorInclusion k N x ∈ completeModule M :=
  Submodule.subset_span ⟨x,hx,rfl⟩

/-- The two natural maps form the usual span/inverse-image adjunction. -/
theorem complete_le_iff (M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N))
    (L : Submodule (PowerSeries k) (LaurentLattice.Ambient k N)) :
    completeModule M ≤ L ↔ M ≤ algebraizeModule L := by
  simp only [completeModule,Submodule.span_le,Set.image_subset_iff]
  rfl

/-- The lower standard t-power on the polynomial side. -/
def polynomialSmall (r : ℕ) : Submodule (Polynomial k) (PolynomialLattice.Ambient k N) :=
  (PolynomialLattice.standardModule k N).map
    (LinearMap.lsmul (Polynomial k) (PolynomialLattice.Ambient k N) (Polynomial.X^r))

/-- The same actual t-power on the completed side. -/
def seriesSmall (r : ℕ) : Submodule (PowerSeries k) (LaurentLattice.Ambient k N) :=
  (LaurentLattice.standardModule k N).map
    (LinearMap.lsmul (PowerSeries k) (LaurentLattice.Ambient k N) (PowerSeries.X^r))

/-- Polynomial monomials may be divided by t inside their Laurent ambient space. -/
theorem algebraize_small (r : ℕ) :
    algebraizeModule (seriesSmall (k := k) (N := N) r) = polynomialSmall r := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,he⟩ := hx
    let z := PolynomialLattice.negPower k N r x
    have hz : PolynomialLattice.vectorInclusion k N z = y := by
      apply PolynomialLattice.series_X_pow_smul_injective k N r
      change (PowerSeries.X : PowerSeries k)^r • PolynomialLattice.vectorInclusion k N
          (PolynomialLattice.negPower k N r x) = (PowerSeries.X : PowerSeries k)^r • y
      rw [← PolynomialLattice.vectorInclusion_X_pow,PolynomialLattice.X_pow_negPower]
      exact he.symm
    have hzS : z ∈ PolynomialLattice.standardModule k N :=
      (PolynomialLattice.vectorInclusion_mem_standard_iff k N z).mp (hz ▸ hy)
    exact ⟨z,hzS,PolynomialLattice.X_pow_negPower k N r x⟩
  · rintro x ⟨z,hz,rfl⟩
    refine ⟨PolynomialLattice.vectorInclusion k N z,
      (PolynomialLattice.vectorInclusion_mem_standard_iff k N z).mpr hz,?_⟩
    exact (PolynomialLattice.vectorInclusion_X_pow k N r z).symm

/-- The coordinate vectors have the same actual images. -/
theorem vectorInclusion_single (i : Fin N) :
    PolynomialLattice.vectorInclusion k N (Pi.single i 1) = Pi.single i 1 := by
  classical
  funext j
  simp [PolynomialLattice.vectorInclusion_apply,Pi.single_apply]

/-- The standard power-series vector is the coordinatewise linear combination
of the included polynomial coordinate vectors. -/
theorem standard_sum (f : Fin N → PowerSeries k) :
    LaurentLattice.standardEmbedding k N f =
      ∑ i : Fin N, f i • PolynomialLattice.vectorInclusion k N (Pi.single i 1) := by
  classical
  funext j
  simp [vectorInclusion_single,LaurentLattice.standardEmbedding,Pi.single_apply,
    Algebra.smul_def]

/-- A polynomial lower bound supplies exactly the corresponding completed lower bound. -/
theorem small_le_complete {M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N)}
    (r : ℕ) (hr : polynomialSmall (k := k) (N := N) r ≤ M) :
    seriesSmall r ≤ completeModule M := by
  classical
  rintro x ⟨y,⟨f,rfl⟩,rfl⟩
  simp only [LinearMap.lsmul_apply]
  rw [standard_sum,Finset.smul_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [smul_comm,← PolynomialLattice.vectorInclusion_X_pow]
  apply Submodule.smul_mem
  apply mem_completeModule
  apply hr
  refine ⟨Pi.single i 1,?_,rfl⟩
  refine ⟨Pi.single i 1,?_⟩
  funext j
  simp [PolynomialLattice.standardEmbedding,Pi.single_apply]

/-- Completion sends the actual standard polynomial lattice to the standard
power-series lattice. -/
theorem complete_standard :
    completeModule (PolynomialLattice.standardModule k N) = LaurentLattice.standardModule k N := by
  apply le_antisymm
  · apply (complete_le_iff _ _).mpr
    intro x hx
    exact (PolynomialLattice.vectorInclusion_mem_standard_iff k N x).mpr hx
  · have hp : polynomialSmall (k := k) (N := N) 0 = PolynomialLattice.standardModule k N := by
      ext x
      simp [polynomialSmall,Submodule.mem_map,LinearMap.lsmul_apply]
    have hs : seriesSmall (k := k) (N := N) 0 = LaurentLattice.standardModule k N := by
      ext x
      simp [seriesSmall,Submodule.mem_map,LinearMap.lsmul_apply]
    simpa only [hs] using small_le_complete (k := k) (N := N) 0 hp.le

/-- Denominator bounds put every completed lattice above a standard t-power. -/
theorem series_lower_bound (Λ : LaurentLattice.Lattice k N) :
    ∃ r : ℕ, seriesSmall (k := k) (N := N) r ≤ Λ.module := by
  obtain ⟨r,hr⟩ := LaurentLattice.exists_X_pow_smul_le Λ (LaurentLattice.standardLattice k N)
  exact ⟨r,by rintro x ⟨y,hy,rfl⟩; exact hr y hy⟩

/-- The same independent argument applies on the polynomial side. -/
theorem polynomial_lower_bound (Λ : PolynomialLattice.Lattice k N) :
    ∃ r : ℕ, polynomialSmall (k := k) (N := N) r ≤ Λ.module := by
  obtain ⟨r,hr⟩ := PolynomialLattice.exists_X_pow_smul_le k N Λ
    (PolynomialLattice.standardLattice k N)
  exact ⟨r,by rintro x ⟨y,hy,rfl⟩; exact hr y hy⟩

/-- A polynomial submodule bounded above by a shifted standard lattice is finite. -/
theorem polynomial_finite_of_upper
    (M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N)) (s : ℕ)
    (hs : ∀ x ∈ M, (Polynomial.X : Polynomial k)^s • x ∈ PolynomialLattice.standardModule k N) :
    M.FG := by
  letI : IsNoetherian (Polynomial k) (PolynomialLattice.standardModule k N) :=
    isNoetherian_of_fg_of_noetherian _ (PolynomialLattice.standardModule_finite k N)
  let f : M →ₗ[Polynomial k] PolynomialLattice.standardModule k N := {
    toFun := fun x => ⟨Polynomial.X^s • x.val,hs x.val x.property⟩
    map_add' := fun x y => Subtype.ext (smul_add _ _ _)
    map_smul' := fun a x => Subtype.ext (smul_comm _ _ _) }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact PolynomialLattice.X_pow_smul_injective k N s
      (congrArg (fun z : PolynomialLattice.standardModule k N => z.val) h)
  letI : Module.Finite (Polynomial k) M := Module.Finite.of_injective f hf
  exact Module.Finite.iff_fg.mp inferInstance

/-- The identical bound gives finite generation over the power-series ring. -/
theorem series_finite_of_upper
    (M : Submodule (PowerSeries k) (LaurentLattice.Ambient k N)) (s : ℕ)
    (hs : ∀ x ∈ M, (PowerSeries.X : PowerSeries k)^s • x ∈ LaurentLattice.standardModule k N) :
    M.FG := by
  letI : IsNoetherian (PowerSeries k) (LaurentLattice.standardModule k N) :=
    isNoetherian_of_fg_of_noetherian _ LaurentLattice.standardModule_finite
  let f : M →ₗ[PowerSeries k] LaurentLattice.standardModule k N := {
    toFun := fun x => ⟨PowerSeries.X^s • x.val,hs x.val x.property⟩
    map_add' := fun x y => Subtype.ext (smul_add _ _ _)
    map_smul' := fun a x => Subtype.ext (smul_comm _ _ _) }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact PolynomialLattice.series_X_pow_smul_injective k N s
      (congrArg (fun z : LaurentLattice.standardModule k N => z.val) h)
  letI : Module.Finite (PowerSeries k) M := Module.Finite.of_injective f hf
  exact Module.Finite.iff_fg.mp inferInstance

/-- A polynomial lower bound proves full Laurent-polynomial span. -/
theorem polynomial_spanning_of_lower
    (M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N)) (r : ℕ)
    (hr : polynomialSmall (k := k) (N := N) r ≤ M) :
    Submodule.span (LaurentPolynomial k) (M : Set (PolynomialLattice.Ambient k N)) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨s,hs⟩ := PolynomialLattice.exists_X_pow_smul_mem k N
    (PolynomialLattice.standardLattice k N) x
  have hm : (Polynomial.X : Polynomial k)^(r+s) • x ∈ M := by
    rw [pow_add,mul_smul]
    exact hr ⟨Polynomial.X^s • x,hs,rfl⟩
  have h := (Submodule.span (LaurentPolynomial k) (M : Set (PolynomialLattice.Ambient k N))).smul_mem
    (LaurentPolynomial.T (-((r+s : ℕ) : ℤ))) (Submodule.subset_span hm)
  convert h using 1
  funext i
  change x i = LaurentPolynomial.T (-((r+s : ℕ) : ℤ)) *
    (Polynomial.toLaurent (Polynomial.X^(r+s)) * x i)
  rw [Polynomial.toLaurent_X_pow,← mul_assoc,← LaurentPolynomial.T_add,
    neg_add_cancel,LaurentPolynomial.T_zero,one_mul]

/-- A completed lower bound proves full Laurent-series span. -/
theorem series_spanning_of_lower
    (M : Submodule (PowerSeries k) (LaurentLattice.Ambient k N)) (r : ℕ)
    (hr : seriesSmall (k := k) (N := N) r ≤ M) :
    Submodule.span (LaurentSeries k) (M : Set (LaurentLattice.Ambient k N)) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨s,hs⟩ := LaurentLattice.exists_X_pow_smul_mem (LaurentLattice.standardLattice k N) x
  have hm : (PowerSeries.X : PowerSeries k)^(r+s) • x ∈ M := by
    rw [pow_add,mul_smul]
    exact hr ⟨PowerSeries.X^s • x,hs,rfl⟩
  let a := algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^(r+s))
  have ha : a ≠ 0 := by
    intro hz
    exact (pow_ne_zero (r+s) PowerSeries.X_ne_zero)
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k) (by simpa [a] using hz))
  have h := (Submodule.span (LaurentSeries k) (M : Set (LaurentLattice.Ambient k N))).smul_mem
    a⁻¹ (Submodule.subset_span hm)
  have he : a⁻¹ • ((PowerSeries.X : PowerSeries k)^(r+s) • x) = x := by
    funext i
    change a⁻¹ * (a * x i) = x i
    rw [← mul_assoc,inv_mul_cancel₀ ha,one_mul]
  rwa [he] at h

/-- Completion respects a polynomial upper bound. -/
theorem complete_upper_bound (M : Submodule (Polynomial k) (PolynomialLattice.Ambient k N))
    (s : ℕ)
    (hs : ∀ x ∈ M, (Polynomial.X : Polynomial k)^s • x ∈ PolynomialLattice.standardModule k N) :
    ∀ y ∈ completeModule M,
      (PowerSeries.X : PowerSeries k)^s • y ∈ LaurentLattice.standardModule k N := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x,hx,rfl⟩ := hy
    rw [← PolynomialLattice.vectorInclusion_X_pow]
    exact (PolynomialLattice.vectorInclusion_mem_standard_iff k N _).mpr (hs x hx)
  | zero => simp
  | add x y hx hy ihx ihy => rw [smul_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => rw [smul_comm]; exact Submodule.smul_mem _ _ ih

/-- Completion of an independent polynomial lattice is an actual full completed lattice. -/
def complete (Λ : PolynomialLattice.Lattice k N) : LaurentLattice.Lattice k N where
  module := completeModule Λ.module
  finite := by
    obtain ⟨s,hs⟩ := PolynomialLattice.exists_X_pow_smul_le k N
      (PolynomialLattice.standardLattice k N) Λ
    exact series_finite_of_upper _ s (complete_upper_bound _ s hs)
  spanning := by
    obtain ⟨r,hr⟩ := polynomial_lower_bound Λ
    exact series_spanning_of_lower _ r (small_le_complete r hr)

/-- Algebraization is an independent finitely generated full polynomial lattice. -/
def algebraize (Λ : LaurentLattice.Lattice k N) : PolynomialLattice.Lattice k N where
  module := algebraizeModule Λ.module
  finite := by
    obtain ⟨s,hs⟩ := LaurentLattice.exists_X_pow_smul_le (LaurentLattice.standardLattice k N) Λ
    apply polynomial_finite_of_upper _ s
    intro x hx
    apply (PolynomialLattice.vectorInclusion_mem_standard_iff k N _).mp
    rw [PolynomialLattice.vectorInclusion_X_pow]
    exact hs _ hx
  spanning := by
    obtain ⟨r,hr⟩ := series_lower_bound Λ
    apply polynomial_spanning_of_lower _ r
    rw [← algebraize_small]
    exact algebraizeModule_mono hr

end Guralnick.LatticeCompletion
