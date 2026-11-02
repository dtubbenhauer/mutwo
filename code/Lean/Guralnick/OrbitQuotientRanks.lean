import Guralnick.OrbitLatticeCuts

/-! # Generic quotient-rank consequences of actual periodic coordinates

These lemmas apply to arbitrary boundary masks, including the one-line
and full-spherical auxiliary galleries. Their hypotheses are equalities
of independently defined subspaces, not a prescribed numerical rank.
-/
noncomputable section
namespace Guralnick.OrbitMatrix
open LaurentLattice AffineLatticePosition LatticeGallery
variable {k : Type*} [Field k] {N : ℕ} [NeZero N]
  (input : CoordinateDimensionInput k N)
  (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) (w : AffinePermutation N)
  (B U : Submodule k (Ambient k N)) (hBU : B ≤ U)

include input

/-- The sum endpoint I=(source cut)+B gives the lower cumulative rank. -/
theorem quotient_lower_intersection (I A : Set.Icc B U) (b : ℕ) (c : ℤ)
    (hB : targetCut k N g 0 = B) (hA : targetCut k N g b = A.val)
    (hI : I.val = sourceCut k N g w c ⊔ B) :
    Module.finrank k ((quotientIntervalIso B U hBU).symm I ⊓
      (quotientIntervalIso B U hBU).symm A : Submodule k (QuotientSpace B U)) =
      cumulativeCount N w 0 b c := by
  rw [quotientImage_inf_finrank]
  have hd := input.cumulative_dimension g w 0 b c (by omega)
  unfold CumulativeQuotient at hd
  rw [hB,hA,← hI,inf_comm] at hd
  exact hd

/-- The intersection endpoint K=(source cut)∩U gives the upper cumulative
rank as soon as the actual lower cut B lies in that source cut. -/
theorem quotient_upper_intersection (K A : Set.Icc B U) (b : ℕ) (c : ℤ)
    (hB : targetCut k N g 0 = B) (hA : targetCut k N g b = A.val)
    (hK : K.val = sourceCut k N g w c ⊓ U)
    (hBK : B ≤ sourceCut k N g w c) :
    Module.finrank k ((quotientIntervalIso B U hBU).symm K ⊓
      (quotientIntervalIso B U hBU).symm A : Submodule k (QuotientSpace B U)) =
      cumulativeCount N w 0 b c := by
  rw [quotientImage_inf_finrank,hK,inf_assoc,inf_eq_right.mpr A.property.2]
  have hd := input.cumulative_dimension g w 0 b c (by omega)
  unfold CumulativeQuotient at hd
  rw [hB,hA,sup_eq_left.mpr hBK,inf_comm] at hd
  exact hd

theorem quotient_lower_rank (I : Set.Icc B U) (b : ℕ) (c : ℤ)
    (hB : targetCut k N g 0 = B) (hU : targetCut k N g b = U)
    (hI : I.val = sourceCut k N g w c ⊔ B) :
    Module.finrank k ((quotientIntervalIso B U hBU).symm I) =
      cumulativeCount N w 0 b c := by
  change Module.finrank k (quotientImage B U hBU I.val I.property.1 I.property.2) = _
  rw [quotientImage_finrank]
  have hd := input.cumulative_dimension g w 0 b c (by omega)
  unfold CumulativeQuotient at hd
  rw [hB,hU,← hI,inf_eq_right.mpr I.property.2] at hd
  exact hd

theorem quotient_upper_rank (K : Set.Icc B U) (b : ℕ) (c : ℤ)
    (hB : targetCut k N g 0 = B) (hU : targetCut k N g b = U)
    (hK : K.val = sourceCut k N g w c ⊓ U)
    (hBK : B ≤ sourceCut k N g w c) :
    Module.finrank k ((quotientIntervalIso B U hBU).symm K) =
      cumulativeCount N w 0 b c := by
  change Module.finrank k (quotientImage B U hBU K.val K.property.1 K.property.2) = _
  rw [quotientImage_finrank,hK]
  have hd := input.cumulative_dimension g w 0 b c (by omega)
  unfold CumulativeQuotient at hd
  rw [hB,hU,sup_eq_left.mpr hBK,inf_comm] at hd
  exact hd

end Guralnick.OrbitMatrix
