import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Div

/-!
# The actual polynomial-to-power-series map on finite quotients

The natural inclusion k[t] → k[[t]] induces an isomorphism modulo t^d,
including d=0. Injectivity follows by comparing the first d coefficients;
surjectivity uses the actual polynomial truncation of a power series.
This is the finite-quotient step in the completed-lattice comparison,
not yet a comparison of arbitrary full lattices or affine flag convolution.
-/
noncomputable section
namespace Guralnick.PowerSeriesCompletion
variable (k : Type*) [CommRing k] (d : ℕ)

def polynomialIdeal : Ideal (Polynomial k) :=
  Ideal.span {(Polynomial.X : Polynomial k) ^ d}

def seriesIdeal : Ideal (PowerSeries k) :=
  Ideal.span {(PowerSeries.X : PowerSeries k) ^ d}

abbrev PolynomialQuotient := Polynomial k ⧸ polynomialIdeal k d
abbrev SeriesQuotient := PowerSeries k ⧸ seriesIdeal k d

/-- The ordinary inclusion of polynomials, with unchanged coefficients. -/
def inclusion : Polynomial k →ₐ[k] PowerSeries k :=
  { Polynomial.coeToPowerSeries.ringHom with
    commutes' := by intro a; simp [PowerSeries.algebraMap_apply] }

@[simp] theorem inclusion_apply (f : Polynomial k) : inclusion k f = (f : PowerSeries k) := rfl

/-- Divisibility by t^d is detected by exactly the same coefficients. -/
theorem inclusion_mem_iff (f : Polynomial k) :
    inclusion k f ∈ seriesIdeal k d ↔ f ∈ polynomialIdeal k d := by
  simp only [seriesIdeal, polynomialIdeal, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff, inclusion_apply,
    Polynomial.coeff_coe]

/-- The induced natural map on the actual ideal quotients. -/
def completion : PolynomialQuotient k d →ₐ[k] SeriesQuotient k d :=
  Ideal.Quotient.liftₐ (polynomialIdeal k d)
    ((Ideal.Quotient.mkₐ k (seriesIdeal k d)).comp (inclusion k))
    (by
      intro f hf
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((inclusion_mem_iff k d f).mpr hf))

@[simp] theorem completion_mk (f : Polynomial k) :
    completion k d (Ideal.Quotient.mk (polynomialIdeal k d) f) =
      Ideal.Quotient.mk (seriesIdeal k d) (f : PowerSeries k) := rfl

/-- Completion loses no class in the finite polynomial quotient. -/
theorem completion_injective : Function.Injective (completion k d) := by
  apply RingHom.lift_injective_of_ker_le_ideal (polynomialIdeal k d)
  intro f hf
  exact (inclusion_mem_iff k d f).mp (Ideal.Quotient.eq_zero_iff_mem.mp hf)

/-- The finite truncation represents the original power series modulo t^d. -/
theorem trunc_class (f : PowerSeries k) :
    Ideal.Quotient.mk (seriesIdeal k d) ((PowerSeries.trunc d f : Polynomial k) : PowerSeries k) =
      Ideal.Quotient.mk (seriesIdeal k d) f := by
  apply Ideal.Quotient.eq.mpr
  rw [seriesIdeal, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro i hi
  simp [PowerSeries.coeff_trunc, hi]

/-- Every completed class has an actual polynomial representative. -/
theorem completion_surjective : Function.Surjective (completion k d) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk (polynomialIdeal k d) (PowerSeries.trunc d f),
    trunc_class k d f⟩

/-- The isomorphism is induced by the natural inclusion, not an arbitrary
identification of two vector spaces of the same dimension. -/
def completionEquiv : PolynomialQuotient k d ≃ₐ[k] SeriesQuotient k d :=
  AlgEquiv.ofBijective (completion k d)
    ⟨completion_injective k d, completion_surjective k d⟩

@[simp] theorem completionEquiv_mk (f : Polynomial k) :
    completionEquiv k d (Ideal.Quotient.mk (polynomialIdeal k d) f) =
      Ideal.Quotient.mk (seriesIdeal k d) (f : PowerSeries k) := rfl

/-- Multiplication by the actual parameter is respected. -/
theorem completion_parameter_mul (x : PolynomialQuotient k d) :
    completionEquiv k d (Ideal.Quotient.mk (polynomialIdeal k d) Polynomial.X * x) =
      Ideal.Quotient.mk (seriesIdeal k d) PowerSeries.X * completionEquiv k d x := by
  rw [map_mul, completionEquiv_mk, Polynomial.coe_X]

#print axioms completionEquiv
end Guralnick.PowerSeriesCompletion
