import Guralnick.FiniteFlagEnumerationFrames

/-! # Quotient intervals and actual finite-subspace enumeration -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.FiniteFlagEnumeration
open GalleryCounting CanonicalGallery
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

theorem quotient_map_finrank (S U : Submodule k V) (h : S ≤ U) :
    Module.finrank k (U.map S.mkQ) + Module.finrank k S = Module.finrank k U := by
  have hf := (S.mkQ.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict] at hf
  have hk : LinearMap.ker (S.mkQ.domRestrict U) = S.comap U.subtype := by
    ext x
    simp
  rw [hk,(Submodule.comapSubtypeEquivOfLe h).finrank_eq] at hf
  exact hf

def upperIntervalEquiv (lo up : Submodule k V) (h : lo ≤ up) (j : ℕ) :
    IntermediateSubspace lo up j ≃
      {U : Submodule k up // lo.comap up.subtype ≤ U ∧ Module.finrank k U = j} where
  toFun U := ⟨U.val.comap up.subtype,Submodule.comap_mono U.property.1,by
    rw [(Submodule.comapSubtypeEquivOfLe U.property.2.1).finrank_eq]
    exact U.property.2.2⟩
  invFun U := ⟨U.val.map up.subtype,by
    have hh := Submodule.map_mono (f := up.subtype) U.property.1
    simpa [Submodule.map_comap_subtype,inf_of_le_right h] using hh,
    Submodule.map_subtype_le up U.val,by simpa using U.property.2⟩
  left_inv U := by
    apply Subtype.ext
    change (U.val.comap up.subtype).map up.subtype = U.val
    simp [Submodule.map_comap_subtype,inf_of_le_right U.property.2.1]
  right_inv U := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective U.val

def quotientGrassmannEquiv (S : Submodule k V) (j : ℕ)
    (hj : Module.finrank k S ≤ j) :
    {U : Submodule k V // S ≤ U ∧ Module.finrank k U = j} ≃
      Grassmann k (V ⧸ S) (j-Module.finrank k S) where
  toFun U := ⟨U.val.map S.mkQ,by
    have := quotient_map_finrank S U.val U.property.1
    omega⟩
  invFun U := ⟨U.val.comap S.mkQ,Submodule.le_comap_mkQ S U.val,by
    have hh := quotient_map_finrank S (U.val.comap S.mkQ) (Submodule.le_comap_mkQ S U.val)
    rw [Submodule.map_comap_eq_self (by simp)] at hh
    have := U.property
    omega⟩
  left_inv U := by
    apply Subtype.ext
    change (U.val.map S.mkQ).comap S.mkQ = U.val
    rw [Submodule.comap_map_mkQ,sup_of_le_right U.property.1]
  right_inv U := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

/-- Restricting to the upper space and quotienting the lower space gives
an equivalence of actual subspaces, with the dimension shift proved. -/
def intervalGrassmannEquiv (lo up : Submodule k V) (h : lo ≤ up) (j : ℕ)
    (hj : Module.finrank k lo ≤ j) :
    IntermediateSubspace lo up j ≃
      Grassmann k (up ⧸ lo.comap up.subtype) (j-Module.finrank k lo) := by
  have he := (Submodule.comapSubtypeEquivOfLe h).finrank_eq
  exact (upperIntervalEquiv lo up h j).trans
    ((quotientGrassmannEquiv (lo.comap up.subtype) j (by rwa [he])).trans
      (Equiv.cast (by rw [he])))

theorem interval_quotient_finrank (lo up : Submodule k V) (h : lo ≤ up) :
    Module.finrank k (up ⧸ lo.comap up.subtype) =
      Module.finrank k up - Module.finrank k lo := by
  rw [Submodule.finrank_quotient,(Submodule.comapSubtypeEquivOfLe h).finrank_eq]

theorem subspaces [Finite k] [Finite V] (lo up : Submodule k V) (j : ℕ) (h : lo ≤ up) :
    (Nat.card (IntermediateSubspace lo up j) : ℤ) = eval (Nat.card k : ℤ)
      (qGauss ((Module.finrank k up : ℤ)-Module.finrank k lo)
        ((j : ℤ)-Module.finrank k lo)) := by
  classical
  have hlo := Submodule.finrank_mono h
  letI : Finite (up ⧸ lo.comap up.subtype) :=
    Finite.of_surjective (lo.comap up.subtype).mkQ (lo.comap up.subtype).mkQ_surjective
  by_cases hjlo : Module.finrank k lo ≤ j
  · by_cases hjup : j ≤ Module.finrank k up
    · rw [Nat.card_congr (intervalGrassmannEquiv lo up h j hjlo),
        grassmann_cardinality (j-Module.finrank k lo) (by
          rw [interval_quotient_finrank lo up h]; omega),
        interval_quotient_finrank lo up h]
      congr 1
      rw [← Nat.cast_sub hlo,← Nat.cast_sub hjlo,qGauss_nat (by omega)]
    · haveI : IsEmpty (IntermediateSubspace lo up j) := ⟨by
        intro U
        have hh := Submodule.finrank_mono U.property.2.1
        have := U.property.2.2
        omega⟩
      simp only [Nat.card_of_isEmpty,Nat.cast_zero]
      rw [qGauss,if_neg (by omega),eval_zero]
  · haveI : IsEmpty (IntermediateSubspace lo up j) := ⟨by
      intro U
      have hh := Submodule.finrank_mono U.property.1
      have := U.property.2.2
      omega⟩
    simp only [Nat.card_of_isEmpty,Nat.cast_zero]
    rw [qGauss,if_neg (by omega),eval_zero]

end Guralnick.FiniteFlagEnumeration
