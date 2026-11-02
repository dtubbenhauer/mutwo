import Guralnick.FiniteFlagEnumeration
import Mathlib.Data.ZMod.Basic

/-! # Boundary and small finite-vector-space checks -/
noncomputable section
open Polynomial
namespace Guralnick.FiniteFlagEnumeration
open GalleryCounting CanonicalGallery

variable {k V : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Finite V]

theorem zero_interval_zero :
    Nat.card (IntermediateSubspace (⊥ : Submodule k V) ⊥ 0) = 1 := by
  have h := subspaces (⊥ : Submodule k V) ⊥ 0 le_rfl
  norm_num [qGauss,Gaussian.qBinomial] at h
  exact_mod_cast h

theorem zero_interval_positive (j : ℕ) :
    Nat.card (IntermediateSubspace (⊥ : Submodule k V) ⊥ (j+1)) = 0 := by
  have h := subspaces (⊥ : Submodule k V) ⊥ (j+1) le_rfl
  simp [qGauss] at h
  exact h

omit [Finite k] [Finite V] in
theorem no_adjacent_flag_in_equal_interval (U : Submodule k V) (m : ℕ) :
    Nat.card (AdjacentFlag U U m) = 0 := by
  haveI : IsEmpty (AdjacentFlag U U m) := ⟨by
    intro f
    have hI := Submodule.finrank_mono f.lower_le
    have hK := Submodule.finrank_mono f.upper_le
    have hm := Submodule.finrank_mono f.middle_le
    have := f.I_dim
    have := f.K_dim
    omega⟩
  exact Nat.card_of_isEmpty

theorem fano_lines : Nat.card (Grassmann (ZMod 2) (Fin 3 → ZMod 2) 1) = 7 := by
  have h := grassmann_cardinality (k := ZMod 2) (V := Fin 3 → ZMod 2) 1 (by simp)
  norm_num [Gaussian.qBinomial] at h
  exact_mod_cast h

theorem fano_planes : Nat.card (Grassmann (ZMod 2) (Fin 3 → ZMod 2) 2) = 7 := by
  have h := grassmann_cardinality (k := ZMod 2) (V := Fin 3 → ZMod 2) 2 (by simp)
  norm_num [Gaussian.qBinomial] at h
  exact_mod_cast h

theorem fano_flags : Nat.card
    (AdjacentFlag (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2)) ⊤ 1) = 21 := by
  have h := adjacent (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2)) ⊤ 1 bot_le
  norm_num [qGauss,qInt,Int.toNat,Gaussian.qBinomial,Gaussian.qInteger,
    Finset.sum_range_succ] at h
  exact_mod_cast h

#print axioms fano_flags
#print axioms no_adjacent_flag_in_equal_interval
end Guralnick.FiniteFlagEnumeration
