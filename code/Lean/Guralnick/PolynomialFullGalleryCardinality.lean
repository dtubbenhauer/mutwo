import Guralnick.PolynomialFullGalleryEquiv
import Guralnick.PolynomialFullLiftCardinality

/-! # The full-to-partial gallery count

The configuration equivalence records a full lift of each actual common
facet. The cardinality of each lift was obtained from the symmetrizer
square. Counting this explicit dependent sum gives exactly the product
of Poincare factors cancelled in normalized partial-flag convolution.
-/
noncomputable section
namespace Guralnick.PolynomialFullGallery
open scoped BigOperators
open Hecke ParabolicWeb CanonicalChains LatticeFlags PolynomialFlags
open PolynomialConvolutionNormalization
variable {n : ℕ} [NeZero n] {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)
variable (p : ℕ) [Fact p.Prime] (hp : p.Prime)
variable (C : FullFlagHeckeConvolution.Input K p hp)
include L C


theorem decorations_card {I J : Index n} (path : Chain I J)
    {source : PolynomialFlags.Flag (GaloisField p 2) n (retained I)}
    {target : PolynomialFlags.Flag (GaloisField p 2) n (retained J)}
    (g : PolynomialFlags.Gallery path source target) :
    (Nat.card (Decorations path g) : ℚ) = poincareProduct D p path := by
  induction path with
  | nil => simp only [Decorations,poincareProduct,Nat.card_unique,Nat.cast_one]
  | snoc path T ih =>
      simp only [Decorations,Nat.card_prod,Nat.cast_mul,poincareProduct]
      rw [ih,PolynomialFullLiftCardinality.lift_card_eq K D L p hp C]

/-- A bijection of actual configurations, followed by a finite dependent
sum, gives the full-gallery/partial-gallery Poincare factor. -/
theorem fullGallery_card {I J : Index n} (path : Chain I J)
    (source target : FullFlag (GaloisField p 2) n) :
    (Nat.card (FullGallery path source target) : ℚ) =
      poincareProduct D p path *
        (Nat.card (PolynomialFlags.Gallery path (forget I source) (forget J target)) : ℚ) := by
  classical
  letI := PolynomialFlags.gallery_finite path (forget I source) (forget J target)
  letI := Fintype.ofFinite
    (PolynomialFlags.Gallery path (forget I source) (forget J target))
  rw [Nat.card_congr (configurationEquiv path source target),Nat.card_sigma,Nat.cast_sum]
  simp_rw [decorations_card K D L p hp C path]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  exact mul_comm _ _

#print axioms decorations_card
#print axioms fullGallery_card
end Guralnick.PolynomialFullGallery
