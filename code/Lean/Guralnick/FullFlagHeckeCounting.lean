import Guralnick.FullFlagHeckeConvolution
import Guralnick.PolynomialConvolutionNormalization

/-! # Products of actual parabolic indicators count actual full galleries

This is induction from binary full-flag convolution. Its middle objects are
literal full polynomial flags and its fibers are the defined FullGallery
types. The theorem does not assume an arbitrary-chain convolution formula.
-/
noncomputable section
namespace Guralnick.FullFlagHeckeConvolution
open Hecke ParabolicWeb CanonicalChains PolynomialFullGallery PolynomialsFromCounts
open PolynomialConvolutionNormalization
open scoped BigOperators Classical
variable {n : ℕ} [NeZero n] {k : Type} [Field k]

/-- Group the last full middle flag by its actual retained target flag. -/
def lastLiftEquiv {I J : Index n} (path : Chain I J) (T : Index n)
    (source target : FullFlag k n) :
    FullGallery (.snoc path T) source target ≃
      ((E : Lift (forget T target)) × FullGallery path source E.val) := by
  simp only [FullGallery]
  exact {
    toFun := fun g => ⟨⟨g.1,g.2.2.down⟩,g.2.1⟩
    invFun := fun g => ⟨g.1.val,g.2,⟨g.1.property⟩⟩
    left_inv := fun g => by cases g; rfl
    right_inv := fun g => by cases g; rfl }

/-- Finiteness follows by choosing the last full lift, independently of
any convolution theorem or partial-gallery decoration count. -/
theorem fullGalleryFiniteByLifts [Finite k] {I J : Index n} (path : Chain I J)
    (source target : FullFlag k n) : Finite (FullGallery path source target) := by
  induction path generalizing target with
  | nil => simp only [FullGallery]; infer_instance
  | snoc path T ih =>
      haveI (E : Lift (forget T target)) : Finite (FullGallery path source E.val) := ih E.val
      exact Finite.of_equiv _ (lastLiftEquiv path T source target).symm

attribute [local instance] fullGalleryFiniteByLifts

theorem card_nil (I : Index n) (source target : FullFlag k n) :
    Nat.card (FullGallery (.nil I) source target) =
      if forget I source=forget I target then 1 else 0 := by
  simp only [FullGallery]
  by_cases h : forget I source=forget I target
  · letI : Nonempty (PLift (forget I source=forget I target)) := ⟨⟨h⟩⟩
    rw [if_pos h,Nat.card_unique]
  · letI : IsEmpty (PLift (forget I source=forget I target)) := ⟨fun a => h a.down⟩
    rw [if_neg h]
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem card_snoc [Finite k] {I J : Index n} (path : Chain I J) (T : Index n)
    (source target : FullFlag k n) :
    letI := Fintype.ofFinite (Lift (forget T target))
    (Nat.card (FullGallery (.snoc path T) source target) : ℚ) =
      ∑ E : Lift (forget T target), (Nat.card (FullGallery path source E.val) : ℚ) := by
  letI := Fintype.ofFinite (Lift (forget T target))
  rw [Nat.card_congr (lastLiftEquiv path T source target),Nat.card_sigma,Nat.cast_sum]

variable {c : WindowCoxeter n} (K : KLRealization c) (p : ℕ) [Fact p.Prime] (hp : p.Prime)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)
include L

/-- Binary convolution successively introduces one actual full middle flag. -/
theorem value_numerator_count (C : Input K p hp) {I J : Index n} (path : Chain I J)
    (source target : FullFlag (GaloisField p 2) n) :
    value K p hp C.orbits (Chain.numerator K D path) target source =
      ((primeUnit p hp)^(vertexWeight D path)).val *
        (Nat.card (FullGallery path source target) : ℚ) := by
  induction path generalizing target with
  | nil =>
      rw [Chain.numerator,value_symmetrizer K p hp D L,card_nil]
      by_cases h : forget I source=forget I target <;>
        simp only [vertexWeight,h,if_true,if_false,Nat.cast_one,Nat.cast_zero,mul_one,mul_zero]
  | @snoc J path T ih =>
      letI : Finite {E : FullFlag (GaloisField p 2) n // forget T E=forget T target} :=
        inferInstanceAs (Finite (Lift (forget T target)))
      letI : Fintype {E : FullFlag (GaloisField p 2) n // forget T E=forget T target} :=
        Fintype.ofFinite _
      letI := Fintype.ofFinite (Lift (forget T target))
      rw [Chain.numerator,C.convolution]
      have he : (∑ᶠ middle : FullFlag (GaloisField p 2) n,
          value K p hp C.orbits (symmetrizer K D T) target middle *
            value K p hp C.orbits (Chain.numerator K D path) middle source) =
          ∑ᶠ middle : FullFlag (GaloisField p 2) n,
            if forget T middle=forget T target then
              ((primeUnit p hp)^(vertexWeight D (.snoc path T))).val *
                (Nat.card (FullGallery path source middle) : ℚ) else 0 := by
        apply finsum_congr
        intro middle
        rw [value_symmetrizer K p hp D L,ih]
        by_cases hm : forget T middle=forget T target
        · rw [if_pos hm,if_pos hm,vertexWeight,zpow_add,Units.val_mul]
          ring
        · rw [if_neg hm,if_neg hm,zero_mul]
      rw [he,finsum_indicator,card_snoc,Finset.mul_sum]
      change (∑ E : Lift (forget T target), _) = _
      rfl

/-- The normalized standard coefficient of the numerator is derived from
actual binary full-flag convolution, with the precise endpoint exponent. -/
theorem numerator_coordinate_count (C : Input K p hp) {I J : Index n} (path : Chain I J)
    (source target : FullFlag (GaloisField p 2) n) (w : AffinePermutation n)
    (hpos : RelativePosition target source w) :
    specialize p hp (K.standard.repr (Chain.numerator K D path) w) =
      ((primeUnit p hp)^(vertexWeight D path-c.system.length w)).val *
        (Nat.card (FullGallery path source target) : ℚ) := by
  have h := value_numerator_count K p hp D L C path source target
  rw [value,position_eq C.orbits hpos] at h
  apply mul_left_cancel₀ (Units.ne_zero ((primeUnit p hp)^(c.system.length w : ℤ)))
  rw [h,←mul_assoc,←Units.val_mul,←zpow_add]
  congr 2
  ring

#print axioms lastLiftEquiv
#print axioms value_numerator_count
#print axioms numerator_coordinate_count
end Guralnick.FullFlagHeckeConvolution
