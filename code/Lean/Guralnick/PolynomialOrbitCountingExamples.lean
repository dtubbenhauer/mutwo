import Guralnick.PolynomialOrbitCounting

/-! # Empty, reversed and signed-cut checks for the actual quotient formulas -/
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace Guralnick.PolynomialOrbitCounting
open PolynomialOrbitCoordinates
variable (k : Type) [Field k] (N : ℕ) [NeZero N]

/-- Equal row cuts give the zero relative block quotient. -/
theorem block_zero_width (w : AffinePermutation N) (a c d : ℤ) :
    Module.finrank k (BlockQuotient k N w a a c d) = 0 := by
  rw [block_dimension]
  simp [OrbitMatrix.blockCount]

/-- The basis calculation handles reversed row bounds, without assigning
an arbitrary default dimension to an uncontrolled infinite quotient. -/
theorem block_reversed_row (w : AffinePermutation N) (a b c d : ℤ) (h : b ≤ a) :
    Module.finrank k (BlockQuotient k N w a b c d) = 0 := by
  rw [block_dimension]
  simp [OrbitMatrix.blockCount,Finset.Ioc_eq_empty_of_le h]

theorem cumulative_zero_width (w : AffinePermutation N) (a c : ℤ) :
    Module.finrank k (CumulativeQuotient k N w a a c) = 0 := by
  rw [cumulative_dimension]
  simp [OrbitMatrix.cumulativeCount]

/-- A signed-cut example in ambient rank five: the surviving labels are 0 and 1. -/
example : Module.finrank ℚ (BlockQuotient ℚ 5 (1 : AffinePermutation 5) (-3) 1 (-1) 2) = 2 := by
  rw [block_dimension]
  have h : (1 : AffinePermutation 5).onIntegers = Equiv.refl ℤ := by
    ext z
    simp [AffinePermutation.onIntegers,AffinePermutation.equiv_one]
  simp only [OrbitMatrix.blockCount,h,Equiv.refl_symm,Equiv.refl_apply]
  decide

/-- Rank one is also covered by the coordinate model and the uniform proof. -/
example : Module.finrank ℚ (CumulativeQuotient ℚ 1 (1 : AffinePermutation 1) 0 3 2) = 2 := by
  rw [cumulative_dimension]
  have h : (1 : AffinePermutation 1).onIntegers = Equiv.refl ℤ := by
    ext z
    simp [AffinePermutation.onIntegers,AffinePermutation.equiv_one]
  simp only [OrbitMatrix.cumulativeCount,h,Equiv.refl_symm,Equiv.refl_apply]
  decide

end Guralnick.PolynomialOrbitCounting
