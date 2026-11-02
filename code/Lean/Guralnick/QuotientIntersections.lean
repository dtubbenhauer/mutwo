import Guralnick.RelativeDimensions

namespace Guralnick.LatticeGallery
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The quotient order correspondence preserves actual intersections, and
their dimensions are those of the corresponding ambient subquotients. -/
theorem quotientImage_inf_finrank (B U : Submodule k V) (hBU : B ≤ U)
    (A C : Set.Icc B U) :
    Module.finrank k
      ((quotientIntervalIso B U hBU).symm A ⊓ (quotientIntervalIso B U hBU).symm C :
        Submodule k (QuotientSpace B U)) =
      Module.finrank k (QuotientSpace B (A.val ⊓ C.val)) := by
  rw [← (quotientIntervalIso B U hBU).symm.map_inf]
  exact quotientImage_finrank B U hBU (A.val ⊓ C.val)
    (le_inf A.property.1 C.property.1) (inf_le_left.trans A.property.2)

end Guralnick.LatticeGallery
