import Guralnick.Cohomology

/-!
# Finite dimensionality of actual finite-group first cohomology

This removes a redundant application hypothesis: one-cocycles form a
subspace of the finite function space `G → A`, and their canonical map
onto first cohomology is surjective.
-/

noncomputable section
namespace Guralnick.Cohomology
open CategoryTheory

variable {k G : Type} [Field k] [Group G] [Finite G]

theorem finiteDimensional_H1 (A : Rep k G) [FiniteDimensional k A] :
    FiniteDimensional k (H1 A) := by
  letI := Fintype.ofFinite G
  letI : FiniteDimensional k (groupCohomology.oneCocycles A) := inferInstance
  exact FiniteDimensional.of_surjective (groupCohomology.H1π A).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end Guralnick.Cohomology
