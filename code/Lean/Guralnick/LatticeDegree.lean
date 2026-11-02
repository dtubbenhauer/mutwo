import Guralnick.LatticeOperations
import Guralnick.RelativeDegreeAdditivity

/-!
# The actual lattice degree is the relative quotient dimension

The reference object is the actual standard lattice. Its intersections
with full lattices are constructed full lattices, so finite-dimensionality
of every quotient used below follows from the proved lattice quotient
result. Signed-index cancellation then gives the exact degree convention
used in the manuscript and existing flag definitions.
-/
noncomputable section
namespace Guralnick.LaurentLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- The manuscript's signed degree difference is the dimension of the
actual nested lattice quotient. No lattice-theory input occurs. -/
theorem dimension_degree (Λ M : Lattice k N) (hΛM : Λ ≤ M) :
    (Module.finrank k (LatticeGallery.QuotientSpace Λ.space M.space) : ℤ) =
      degree k N M - degree k N Λ := by
  let S := standardLattice k N
  let I := interLattice Λ S
  letI : FiniteDimensional k (LatticeGallery.QuotientSpace (Λ.space ⊓ S.space) M.space) :=
    finite_quotient I M (le_trans (interLattice_le_left Λ S) hΛM)
  letI : FiniteDimensional k (LatticeGallery.QuotientSpace (Λ.space ⊓ S.space) S.space) :=
    finite_quotient I S (interLattice_le_right Λ S)
  exact LatticeGallery.relative_degree_difference Λ.space M.space S.space hΛM

#print axioms dimension_degree
end Guralnick.LaurentLattice
