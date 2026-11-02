import Guralnick.RelativeDimensions

/-! Signed relative index against a fixed reference subspace is additive.
The finiteness assumptions are on actual quotient spaces, so finrank is
never used as a substitute for an unproved finite-dimensionality claim. -/
noncomputable section
namespace Guralnick.LatticeGallery
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Relative degree changes by the dimension of an actual nested quotient.
This is the general vector-space calculation needed for lattice degrees. -/
theorem relative_degree_difference (Λ M S : Submodule k V) (hΛM : Λ ≤ M)
    [FiniteDimensional k (QuotientSpace (Λ ⊓ S) M)]
    [FiniteDimensional k (QuotientSpace (Λ ⊓ S) S)] :
    (Module.finrank k (QuotientSpace Λ M) : ℤ) =
      ((Module.finrank k (QuotientSpace (M ⊓ S) M) : ℤ) -
        Module.finrank k (QuotientSpace (M ⊓ S) S)) -
      ((Module.finrank k (QuotientSpace (Λ ⊓ S) Λ) : ℤ) -
        Module.finrank k (QuotientSpace (Λ ⊓ S) S)) := by
  have h₁ := quotient_chain_dimensions (Λ ⊓ S) Λ M inf_le_left hΛM
  have h₂ := quotient_chain_dimensions (Λ ⊓ S) (M ⊓ S) M
    (inf_le_inf_right S hΛM) inf_le_left
  have h₃ := quotient_chain_dimensions (Λ ⊓ S) (M ⊓ S) S
    (inf_le_inf_right S hΛM) inf_le_right
  omega

#print axioms relative_degree_difference
end Guralnick.LatticeGallery
