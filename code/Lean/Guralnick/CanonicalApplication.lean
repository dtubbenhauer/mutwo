import Guralnick.ParabolicWeb
import Guralnick.CanonicalGallery
import Guralnick.CanonicalMatrix

/-!
# Applying the support calculation to the actual six-map element

The vector below is `ParabolicWeb.Family.raw`, the composite of six actual
integral module maps. Bar symmetry, cleared positivity and the coefficient
identity are now proved from the generic Hecke/parabolic literature input.
The remaining input in each theorem is explicitly the original manuscript's
gallery-count identification for the chosen ordinary standard coordinate.
It is not classified as a theorem imported from the literature.
-/

noncomputable section

namespace Guralnick.CanonicalApplication

open scoped BigOperators
open Hecke Positivity ParabolicWeb

variable {m : ℕ} {c : WindowCoxeter (2*m+1)}
variable (K : KLRealization c) (D : ∀ I : Index (2*m+1), LongestData c I)
variable (L : Laws K D) (P : PositivityInput K)

theorem scalar_nonnegative (I : Index (2*m+1)) : Nonnegative (scalar D I) := by
  classical
  unfold scalar
  apply nonnegative_sum
  intro w _ n
  simp only [LaurentPolynomial.T_apply]
  split_ifs <;> omega

theorem denominator_nonnegative :
    Nonnegative (scalar D (Family.output m) * scalar D (Family.common m)^2) := by
  rw [pow_two]
  exact nonnegative_mul (scalar_nonnegative D _)
    (nonnegative_mul (scalar_nonnegative D _) (scalar_nonnegative D _))

include P

/-- Six-position support for the actual Hecke element. The only original
calculation still supplied here is the equality `hcount`; all support and
degree hypotheses previously needed by `DegreeBounds` have been discharged. -/
theorem raw_six_positions (w : AffinePermutation (2*m+1)) (l a s β δ : ℤ)
    (hl : 1 ≤ l) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hrow : DegreeBounds.MiddleRow β δ) (hfeas : δ = 0 → 1 ≤ s)
    (hH : s+δ-1 ≤ l+a+β) (hL : a ≤ l+s)
    (hcount : K.standard.repr (Family.raw K D L) w =
      normalize (CanonicalGallery.gap l a s β δ) (CanonicalGallery.count l a s β δ))
    (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    DegreeBounds.SixPositions β δ a s := by
  obtain ⟨rest, hrest, hidentity⟩ := positive_cleared_coordinate_identity K P
    (scalar D (Family.output m) * scalar D (Family.common m)^2)
    (Family.raw K D L) (Family.raw_cleared_nonnegative K D L P) w
  rw [hcount] at hidentity
  exact CanonicalGallery.six_positions_of_count l a s β δ hl ha hs hrow hfeas hH hL
    (Family.denominator_ne_zero K D L) (Family.raw_cleared_nonnegative K D L P w)
    hrest hidentity (Family.raw_canonical_bar K D L w) hne

theorem raw_boundary_position (w : AffinePermutation (2*m+1)) (a s β δ : ℤ)
    (ha : 0 ≤ a) (hrow : DegreeBounds.MiddleRow β δ)
    (hfirst : a ≤ s) (hlast : s ≤ a+1-δ+β)
    (hcount : K.standard.repr (Family.raw K D L) w =
      normalize (CanonicalGallery.gap 0 a s β δ) (CanonicalGallery.count 0 a s β δ))
    (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    β = 0 ∧ δ = 1 ∧ a = 1 ∧ s = 1 := by
  obtain ⟨rest, hrest, hidentity⟩ := positive_cleared_coordinate_identity K P
    (scalar D (Family.output m) * scalar D (Family.common m)^2)
    (Family.raw K D L) (Family.raw_cleared_nonnegative K D L P) w
  rw [hcount] at hidentity
  exact CanonicalGallery.boundary_position_of_count a s β δ ha hrow hfirst hlast
    (Family.denominator_ne_zero K D L) (Family.raw_cleared_nonnegative K D L P w)
    hrest hidentity (Family.raw_canonical_bar K D L w) hne

theorem raw_typeF_zero_or_one (w : AffinePermutation (2*m+1)) (l : ℕ)
    (hcount : K.standard.repr (Family.raw K D L) w =
      normalize (CanonicalGallery.gap l 1 1 0 1) (CanonicalGallery.count l 1 1 0 1)) :
    K.canonical.repr (Family.raw K D L) w = 0 ∨
      K.canonical.repr (Family.raw K D L) w = 1 := by
  obtain ⟨rest, hrest, hidentity⟩ := positive_cleared_coordinate_identity K P
    (scalar D (Family.output m) * scalar D (Family.common m)^2)
    (Family.raw K D L) (Family.raw_cleared_nonnegative K D L P) w
  rw [hcount] at hidentity
  exact CanonicalGallery.typeF_zero_or_one l
    (Family.denominator_ne_zero K D L) (denominator_nonnegative D)
    (Family.raw_cleared_nonnegative K D L P w) hrest hidentity
    (Family.raw_canonical_bar K D L w)

/-- Support extraction for an actual nonnegative aggregate matrix. Its
parameters, feasibility inequalities and normalization exponent are all
derived from its entries and margins in `CanonicalMatrix`. The remaining
original obligation is the displayed equality with the actual standard
coordinate of the integral six-map element. -/
theorem raw_packet_support (w : AffinePermutation (2*m+1))
    (A : CanonicalMatrix.PacketMatrix m)
    (hcount : K.standard.repr (Family.raw K D L) w =
      normalize ((2*(m : ℤ)^2+2*m-3) -
        PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)))
        (CanonicalGallery.count A.corank A.a A.s A.beta A.delta))
    (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    DegreeBounds.SixPositions A.beta A.delta A.a A.s := by
  rw [A.raw_gap] at hcount
  have hnonneg := A.corank_nonnegative
  by_cases hz : A.corank = 0
  · rw [hz] at hcount
    obtain ⟨hb, hd, ha, hs⟩ := raw_boundary_position K D L P w A.a A.s A.beta A.delta
      A.a_nonnegative A.middle_cases (A.boundary_first hz) (A.boundary_last hz)
      hcount hne
    exact Or.inl ⟨hb, hd, Or.inr ha, Or.inr hs⟩
  · exact raw_six_positions K D L P w A.corank A.a A.s A.beta A.delta
      (by omega) A.a_nonnegative A.s_nonnegative A.middle_cases
      A.delta_zero_s_positive A.hyperplane_feasible A.line_feasible hcount hne

/-- At zero corank the only surviving actual matrix is the diagonal member
of the prescribed family. This uses matrix reconstruction, not just a name
assigned to a numerical state. -/
theorem raw_packet_boundary (w : AffinePermutation (2*m+1))
    (A : CanonicalMatrix.PacketMatrix m) (hz : A.corank = 0)
    (hcount : K.standard.repr (Family.raw K D L) w =
      normalize ((2*(m : ℤ)^2+2*m-3) -
        PeriodicMatrix.dimension (fun i j => (A.entries i j : ℤ)))
        (CanonicalGallery.count A.corank A.a A.s A.beta A.delta))
    (hne : K.canonical.repr (Family.raw K D L) w ≠ 0) :
    A.entries = Guralnick.Family.prescribedArray m m := by
  rw [A.raw_gap, hz] at hcount
  obtain ⟨hb, hd, ha, hs⟩ := raw_boundary_position K D L P w A.a A.s A.beta A.delta
    A.a_nonnegative A.middle_cases (A.boundary_first hz) (A.boundary_last hz)
    hcount hne
  have hr : A.rank = m := by
    unfold CanonicalMatrix.PacketMatrix.corank at hz
    omega
  simpa only [hr] using A.typeF_identification ha hs hb hd

end Guralnick.CanonicalApplication
