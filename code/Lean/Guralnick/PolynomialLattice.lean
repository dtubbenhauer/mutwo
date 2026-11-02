import Guralnick.LatticeOperations
import Guralnick.PowerSeriesCompletion
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Polynomial Laurent lattices and their natural embedding

These are independent finitely generated k[t]-submodules of k[t,t⁻¹]^N,
with full span after inverting t. Fullness over k(t) alone would be weaker
and is deliberately not used. The map to the completed ambient space is
induced by the ordinary polynomial inclusion.
-/
noncomputable section
namespace Guralnick.PolynomialLattice
variable (k : Type*) [Field k] (N : ℕ)

instance polynomialScalarTower : IsScalarTower k (Polynomial k) (LaurentPolynomial k) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change LaurentPolynomial.C a = Polynomial.toLaurent (Polynomial.C a)
    exact (Polynomial.toLaurent_C a).symm

abbrev Ambient := Fin N → LaurentPolynomial k

structure Lattice where
  module : Submodule (Polynomial k) (Ambient k N)
  finite : module.FG
  spanning : Submodule.span (LaurentPolynomial k) (module : Set (Ambient k N)) = ⊤

namespace Lattice
variable {k N}
def space (Λ : Lattice k N) : Submodule k (Ambient k N) := Λ.module.restrictScalars k
@[ext] theorem ext {Λ M : Lattice k N} (h : Λ.module = M.module) : Λ = M := by
  cases Λ; cases M; cases h; rfl
instance : PartialOrder (Lattice k N) :=
  PartialOrder.lift Lattice.module (fun _ _ h => ext h)
theorem le_space_iff {Λ M : Lattice k N} : Λ ≤ M ↔ Λ.space ≤ M.space := Iff.rfl
end Lattice

/-- The ordinary polynomial inclusion in Laurent series. -/
def polynomialInclusion : Polynomial k →+* LaurentSeries k :=
  (algebraMap (PowerSeries k) (LaurentSeries k)).comp Polynomial.coeToPowerSeries.ringHom

@[simp] theorem polynomialInclusion_apply (p : Polynomial k) :
    polynomialInclusion k p = algebraMap (PowerSeries k) (LaurentSeries k) (p : PowerSeries k) := rfl

theorem polynomialInclusion_injective : Function.Injective (polynomialInclusion k) :=
  (IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp (Polynomial.coe_injective k)

/-- Every power of the parameter becomes a unit in Laurent series. -/
theorem polynomialInclusion_units (s : Submonoid.powers (Polynomial.X : Polynomial k)) :
    IsUnit (polynomialInclusion k s) := by
  obtain ⟨n,hn⟩ := s.property
  rw [← hn, map_pow]
  apply IsUnit.pow
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using (polynomialInclusion_injective k).ne Polynomial.X_ne_zero

/-- Natural inclusion of Laurent polynomials, obtained by inverting t. -/
def inclusion : LaurentPolynomial k →+* LaurentSeries k :=
  IsLocalization.lift (polynomialInclusion_units k)

@[simp] theorem inclusion_toLaurent (p : Polynomial k) :
    inclusion k (Polynomial.toLaurent p) = polynomialInclusion k p :=
  IsLocalization.lift_eq _ p

theorem inclusion_injective : Function.Injective (inclusion k) := by
  apply (IsLocalization.lift_injective_iff (polynomialInclusion_units k)).mpr
  intro x y
  exact (Polynomial.toLaurent_injective.eq_iff).trans (polynomialInclusion_injective k).eq_iff.symm

/-- Polynomial linearity uses the actual coefficient inclusion. -/
def vectorInclusion : Ambient k N →ₗ[Polynomial k] LaurentLattice.Ambient k N where
  toFun x i := inclusion k (x i)
  map_add' x y := by funext i; exact map_add _ _ _
  map_smul' p x := by
    funext i
    change inclusion k (Polynomial.toLaurent p * x i) =
      algebraMap (PowerSeries k) (LaurentSeries k) (p : PowerSeries k) * inclusion k (x i)
    rw [map_mul,inclusion_toLaurent,polynomialInclusion_apply]

@[simp] theorem vectorInclusion_apply (x : Ambient k N) (i : Fin N) :
    vectorInclusion k N x i = inclusion k (x i) := rfl

theorem vectorInclusion_injective : Function.Injective (vectorInclusion k N) := by
  intro x y h
  funext i
  exact inclusion_injective k (congrFun h i)

/-- The polynomial coordinate lattice. -/
def standardEmbedding : (Fin N → Polynomial k) →ₗ[Polynomial k] Ambient k N where
  toFun x i := Polynomial.toLaurent (x i)
  map_add' x y := by funext i; exact map_add _ _ _
  map_smul' p x := by funext i; exact map_mul _ _ _

def standardModule : Submodule (Polynomial k) (Ambient k N) :=
  LinearMap.range (standardEmbedding k N)

theorem standardModule_finite : (standardModule k N).FG := by
  unfold standardModule
  exact Module.Finite.iff_fg.mp inferInstance

theorem standardModule_spanning :
    Submodule.span (LaurentPolynomial k) (standardModule k N : Set (Ambient k N)) = ⊤ := by
  classical
  apply top_unique
  rw [← (Pi.basisFun (LaurentPolynomial k) (Fin N)).span_eq]
  apply Submodule.span_mono
  rintro x ⟨i,rfl⟩
  refine ⟨Pi.single i 1,?_⟩
  ext j
  simp [standardEmbedding,Pi.basisFun_apply,Pi.single_apply]

def standardLattice : Lattice k N where
  module := standardModule k N
  finite := standardModule_finite k N
  spanning := standardModule_spanning k N

/-- Clearing denominators in a Laurent polynomial uses powers of t only. -/
theorem clear_denominator (a : LaurentPolynomial k) :
    ∃ d : ℕ, ∃ f : Polynomial k, Polynomial.toLaurent (Polynomial.X^d) * a =
      Polynomial.toLaurent f := by
  obtain ⟨⟨f,s⟩,h⟩ := IsLocalization.surj
    (Submonoid.powers (Polynomial.X : Polynomial k)) a
  obtain ⟨d,hd⟩ := s.property
  exact ⟨d,f,by simpa only [← hd,LaurentPolynomial.algebraMap_eq_toLaurent,mul_comm] using h⟩

theorem X_pow_smul_mem_of_le (Λ : Lattice k N) {x : Ambient k N}
    {r s : ℕ} (h : r ≤ s) (hx : (Polynomial.X : Polynomial k)^r • x ∈ Λ.module) :
    (Polynomial.X : Polynomial k)^s • x ∈ Λ.module := by
  rw [← Nat.sub_add_cancel h,pow_add,mul_smul]
  exact Λ.module.smul_mem _ hx

/-- Fullness after inverting t supplies a t-power denominator. -/
theorem exists_X_pow_smul_mem (Λ : Lattice k N) (x : Ambient k N) :
    ∃ r : ℕ, (Polynomial.X : Polynomial k)^r • x ∈ Λ.module := by
  have hx : x ∈ Submodule.span (LaurentPolynomial k) (Λ.module : Set (Ambient k N)) := by
    rw [Λ.spanning]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0,by simpa using hy⟩
  | zero => exact ⟨0,by simp⟩
  | add y z hy hz iy iz =>
    obtain ⟨r,hr⟩ := iy
    obtain ⟨s,hs⟩ := iz
    refine ⟨max r s,?_⟩
    rw [smul_add]
    exact Λ.module.add_mem
      (X_pow_smul_mem_of_le k N Λ (le_max_left r s) hr)
      (X_pow_smul_mem_of_le k N Λ (le_max_right r s) hs)
  | smul a y hy iy =>
    obtain ⟨r,hr⟩ := iy
    obtain ⟨d,f,hf⟩ := clear_denominator k a
    refine ⟨d+r,?_⟩
    have he : (Polynomial.X : Polynomial k)^(d+r) • (a • y) =
        f • ((Polynomial.X : Polynomial k)^r • y) := by
      funext i
      change Polynomial.toLaurent (Polynomial.X^(d+r)) * (a * y i) =
        Polynomial.toLaurent f * (Polynomial.toLaurent (Polynomial.X^r) * y i)
      rw [pow_add,map_mul,← hf]
      ring
    rw [he]
    exact Λ.module.smul_mem f hr

/-- One denominator works for an entire polynomial lattice. -/
theorem exists_X_pow_smul_le (Λ M : Lattice k N) :
    ∃ r : ℕ, ∀ x ∈ M.module, (Polynomial.X : Polynomial k)^r • x ∈ Λ.module := by
  classical
  obtain ⟨d,g,hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp M.finite
  choose r hr using fun i : Fin d => exists_X_pow_smul_mem k N Λ (g i)
  let b := Finset.univ.sup r
  refine ⟨b,fun x hx => ?_⟩
  rw [← hg] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i,rfl⟩ := hy
    exact X_pow_smul_mem_of_le k N Λ (Finset.le_sup (Finset.mem_univ i)) (hr i)
  | zero => simp
  | add y z hy hz iy iz => rw [smul_add]; exact Λ.module.add_mem iy iz
  | smul a y hy iy => rw [smul_comm]; exact Λ.module.smul_mem a iy

/-- Laurent-polynomial inclusion respects parameter powers exactly. -/
theorem vectorInclusion_X_pow (r : ℕ) (x : Ambient k N) :
    vectorInclusion k N ((Polynomial.X : Polynomial k)^r • x) =
      (PowerSeries.X : PowerSeries k)^r • vectorInclusion k N x := by
  rw [map_smul]
  funext i
  change algebraMap (PowerSeries k) (LaurentSeries k)
      ((Polynomial.X^r : Polynomial k) : PowerSeries k) * _ = _
  rw [Polynomial.coe_pow,Polynomial.coe_X]
  rfl

/-- A Laurent polynomial is a power series exactly when it is a polynomial. -/
theorem inclusion_integral_iff (x : LaurentPolynomial k) :
    (∃ f : PowerSeries k, algebraMap (PowerSeries k) (LaurentSeries k) f = inclusion k x) ↔
      ∃ p : Polynomial k, Polynomial.toLaurent p = x := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨r,p,hp⟩ := clear_denominator k x
    have hh : (p : PowerSeries k) = (PowerSeries.X : PowerSeries k)^r * f := by
      apply IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
      rw [map_mul, hf, ← polynomialInclusion_apply, ← inclusion_toLaurent, ← hp, map_mul,
        inclusion_toLaurent, polynomialInclusion_apply, Polynomial.coe_pow, Polynomial.coe_X]
    have hd : Polynomial.X^r ∣ p := by
      apply Ideal.mem_span_singleton.mp
      apply (PowerSeriesCompletion.inclusion_mem_iff k r p).mp
      change (p : PowerSeries k) ∈ Ideal.span {(PowerSeries.X : PowerSeries k)^r}
      rw [Ideal.mem_span_singleton]
      exact ⟨f,hh⟩
    obtain ⟨q,hq⟩ := hd
    refine ⟨q,?_⟩
    have he : Polynomial.toLaurent (Polynomial.X^r) * Polynomial.toLaurent q =
        Polynomial.toLaurent (Polynomial.X^r) * x := by rw [← map_mul,← hq,hp]
    exact (LaurentPolynomial.isUnit_T (r : ℤ)).mul_left_cancel
      (by simpa only [Polynomial.toLaurent_X_pow] using he)
  · rintro ⟨p,rfl⟩
    exact ⟨(p : PowerSeries k),(inclusion_toLaurent k p).symm⟩

/-- The standard lattice square is an actual inverse-image square. -/
theorem vectorInclusion_mem_standard_iff (x : Ambient k N) :
    vectorInclusion k N x ∈ LaurentLattice.standardModule k N ↔
      x ∈ standardModule k N := by
  constructor
  · rintro ⟨f,hf⟩
    have hi : ∀ i : Fin N, ∃ p : Polynomial k, Polynomial.toLaurent p = x i :=
      fun i => (inclusion_integral_iff k (x i)).mp ⟨f i,congrFun hf i⟩
    choose p hp using hi
    exact ⟨p,funext hp⟩
  · rintro ⟨p,rfl⟩
    exact ⟨fun i => (p i : PowerSeries k),funext fun i => (inclusion_toLaurent k (p i)).symm⟩

/-- Parameter multiplication on the polynomial ambient space is injective. -/
theorem X_pow_smul_injective (r : ℕ) :
    Function.Injective (fun x : Ambient k N => (Polynomial.X : Polynomial k)^r • x) := by
  intro x y h
  funext i
  exact (LaurentPolynomial.isUnit_T (r : ℤ)).mul_left_cancel
    (by simpa only [Pi.smul_apply,Algebra.smul_def,LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X_pow] using congrFun h i)

/-- Multiplication by a negative Laurent monomial, in the independent ambient module. -/
def negPower (r : ℕ) (x : Ambient k N) : Ambient k N :=
  (LaurentPolynomial.T (-(r : ℤ)) : LaurentPolynomial k) • x

theorem X_pow_negPower (r : ℕ) (x : Ambient k N) :
    (Polynomial.X : Polynomial k)^r • negPower k N r x = x := by
  funext i
  change Polynomial.toLaurent (Polynomial.X^r) *
    ((LaurentPolynomial.T (-(r : ℤ)) : LaurentPolynomial k) * x i) = x i
  rw [Polynomial.toLaurent_X_pow,← mul_assoc,← LaurentPolynomial.T_add,
    add_neg_cancel,LaurentPolynomial.T_zero,one_mul]

theorem vectorInclusion_laurent_smul (a : LaurentPolynomial k) (x : Ambient k N) :
    vectorInclusion k N (a • x) = inclusion k a • vectorInclusion k N x := by
  funext i
  exact map_mul (inclusion k) a (x i)

/-- Equality in the completed ambient module is reflected by every t-power. -/
theorem series_X_pow_smul_injective (r : ℕ) : Function.Injective
    (fun x : LaurentLattice.Ambient k N => (PowerSeries.X : PowerSeries k)^r • x) := by
  intro x y h
  funext i
  apply mul_left_cancel₀ (show algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^r) ≠ 0 from
    fun hz => (pow_ne_zero r PowerSeries.X_ne_zero)
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k) (by simpa using hz)))
  exact congrFun h i

theorem vectorInclusion_polynomial_smul (p : Polynomial k) (x : Ambient k N) :
    vectorInclusion k N (p • x) = (p : PowerSeries k) • vectorInclusion k N x := by
  funext i
  change inclusion k (Polynomial.toLaurent p * x i) = _
  rw [map_mul,inclusion_toLaurent]
  rfl

theorem vectorInclusion_standard (p : Fin N → Polynomial k) :
    vectorInclusion k N (standardEmbedding k N p) =
      LaurentLattice.standardEmbedding k N (fun i => (p i : PowerSeries k)) := by
  funext i
  exact inclusion_toLaurent k (p i)

/-- The same natural inclusion as a map of k-algebras. -/
def inclusionAlg : LaurentPolynomial k →ₐ[k] LaurentSeries k :=
  { inclusion k with
    commutes' := by
      intro a
      change inclusion k (LaurentPolynomial.C a) = _
      rw [← Polynomial.toLaurent_C,inclusion_toLaurent,polynomialInclusion_apply,
        Polynomial.coe_C]
      change HahnSeries.ofPowerSeries ℤ k (PowerSeries.C k a) = _
      rw [HahnSeries.ofPowerSeries_C]
      simp [HahnSeries.algebraMap_apply',PowerSeries.algebraMap_apply] }

/-- The natural ambient embedding as a k-linear map. -/
def vectorInclusionLinear : Ambient k N →ₗ[k] LaurentLattice.Ambient k N where
  toFun := vectorInclusion k N
  map_add' := (vectorInclusion k N).map_add
  map_smul' a x := by
    have h := vectorInclusion_polynomial_smul k N (Polynomial.C a) x
    rw [show (Polynomial.C a) • x = a • x from
      IsScalarTower.algebraMap_smul (Polynomial k) a x,
      Polynomial.coe_C,LaurentLattice.C_smul_eq] at h
    exact h

@[simp] theorem vectorInclusionLinear_apply (x : Ambient k N) :
    vectorInclusionLinear k N x = vectorInclusion k N x := rfl

end Guralnick.PolynomialLattice
