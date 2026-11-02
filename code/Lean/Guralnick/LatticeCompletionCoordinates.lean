import Guralnick.LatticeCompletionShift

/-!
# Naturality on explicit Laurent coordinates

The comparison preserves each Laurent monomial, including its signed
winding, and takes a polynomial-generated module to the power-series span
of exactly the same coordinate vectors.
-/
noncomputable section
namespace Guralnick.PolynomialLattice
variable (k : Type*) [Field k]

/-- Signed Laurent exponents are preserved by the natural inclusion. -/
theorem inclusion_T (n : ℤ) :
    inclusion k (LaurentPolynomial.T n) = (HahnSeries.single n 1 : LaurentSeries k) := by
  have hpos : ∀ r : ℕ, inclusion k (LaurentPolynomial.T (r : ℤ)) =
      (HahnSeries.single (r : ℤ) 1 : LaurentSeries k) := by
    intro r
    rw [← Polynomial.toLaurent_X_pow,inclusion_toLaurent,polynomialInclusion_apply,
      Polynomial.coe_pow,Polynomial.coe_X,map_pow]
    change (HahnSeries.ofPowerSeries ℤ k PowerSeries.X)^r = _
    rw [HahnSeries.ofPowerSeries_X,HahnSeries.single_pow]
    simp
  cases n with
  | ofNat r => exact hpos r
  | negSucc r =>
    apply mul_right_cancel₀ (show (HahnSeries.single ((r+1 : ℕ) : ℤ) 1 : LaurentSeries k) ≠ 0 by simp)
    have he : Int.negSucc r + ((r+1 : ℕ) : ℤ) = 0 := by omega
    calc
      inclusion k (LaurentPolynomial.T (Int.negSucc r)) *
          (HahnSeries.single ((r+1 : ℕ) : ℤ) 1 : LaurentSeries k) =
        inclusion k (LaurentPolynomial.T (Int.negSucc r) * LaurentPolynomial.T ((r+1 : ℕ) : ℤ)) := by
          rw [map_mul,hpos]
      _ = 1 := by rw [← LaurentPolynomial.T_add,he,LaurentPolynomial.T_zero,map_one]
      _ = (HahnSeries.single (Int.negSucc r) 1 : LaurentSeries k) *
          HahnSeries.single ((r+1 : ℕ) : ℤ) 1 := by
        rw [HahnSeries.single_mul_single,he,one_mul]
        rfl

/-- The monomial coordinate vector keeps its coordinate and signed exponent. -/
theorem vectorInclusion_monomial {N : ℕ} (i : Fin N) (n : ℤ) :
    vectorInclusion k N (Pi.single i (LaurentPolynomial.T n)) =
      Pi.single i (HahnSeries.single n (1 : k)) := by
  classical
  funext j
  by_cases h : j = i <;> simp [vectorInclusion_apply,Pi.single_apply,h,inclusion_T]

end Guralnick.PolynomialLattice

namespace Guralnick.LatticeCompletion
variable {k : Type*} [Field k] {N : ℕ}

/-- Scalar extension of a polynomial-generated module uses exactly the
same generators, with their natural included coordinates. -/
theorem complete_span (s : Set (PolynomialLattice.Ambient k N)) :
    completeModule (Submodule.span (Polynomial k) s) =
      Submodule.span (PowerSeries k) (PolynomialLattice.vectorInclusion k N '' s) := by
  change Submodule.span (PowerSeries k)
    ((Submodule.span (Polynomial k) s).map (PolynomialLattice.vectorInclusion k N) :
      Set (LaurentLattice.Ambient k N)) = _
  rw [Submodule.map_span,Submodule.span_span_of_tower]

/-- Naturality for any explicitly indexed generating family. -/
theorem complete_span_range {ι : Type*} (v : ι → PolynomialLattice.Ambient k N) :
    completeModule (Submodule.span (Polynomial k) (Set.range v)) =
      Submodule.span (PowerSeries k) (Set.range fun i => PolynomialLattice.vectorInclusion k N (v i)) := by
  rw [complete_span]
  congr 1
  exact (Set.range_comp (PolynomialLattice.vectorInclusion k N) v).symm

#print axioms PolynomialLattice.inclusion_T
#print axioms complete_span
end Guralnick.LatticeCompletion
