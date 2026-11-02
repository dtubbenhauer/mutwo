import Guralnick.FiniteFlagEnumerationIntervals

/-! # Finite flag enumeration, with no counting hypotheses

Hyperplanes and adjacent flags are obtained from the proved subspace
enumeration by actual equivalences. Invalid signed dimensions have empty
configuration spaces and contribute zero, including endpoint dimensions.
-/
noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.FiniteFlagEnumeration
open GalleryCounting CanonicalGallery

theorem qBinomial_self (n : ℕ) : Gaussian.qBinomial n n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Gaussian.qBinomial_succ_succ,
      Gaussian.qBinomial_eq_zero (by omega : n < n+1),ih]

theorem qInteger_succ (n : ℕ) : Gaussian.qInteger (n+1) =
    Gaussian.qInteger n + X^n := by
  simp [Gaussian.qInteger,Finset.sum_range_succ]

theorem qBinomial_one (n : ℕ) : Gaussian.qBinomial n 1 = Gaussian.qInteger n := by
  induction n with
  | zero => simp [Gaussian.qInteger]
  | succ n ih =>
      rw [show 1 = 0+1 from rfl,Gaussian.qBinomial_succ_succ,ih]
      simp only [Gaussian.qBinomial_zero_right]
      unfold Gaussian.qInteger
      rw [Finset.sum_range_succ']
      simp [pow_succ,Finset.mul_sum,add_comm,mul_comm]

theorem qBinomial_codim_one (n : ℕ) (hn : 0 < n) :
    Gaussian.qBinomial n (n-1) = Gaussian.qInteger n := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  induction n with
  | zero => simp [Gaussian.qInteger]
  | succ n ih =>
      change Gaussian.qBinomial (n+1+1) (n+1) = Gaussian.qInteger (n+1+1)
      rw [Gaussian.qBinomial_succ_succ,qBinomial_self,mul_one]
      rw [show Gaussian.qBinomial (n+1) n = Gaussian.qInteger (n+1) by simpa using ih]
      exact (qInteger_succ (n+1)).symm

theorem qGauss_one (n : ℤ) : qGauss n 1 = qInt n := by
  by_cases hn : 1 ≤ n
  · rw [qGauss,if_pos (by omega)]
    simp only [Int.toNat_one,qBinomial_one,qInt]
  · have h : n.toNat = 0 := by omega
    simp [qGauss,qInt,h,hn,Gaussian.qInteger]

theorem qGauss_codim_one {n : ℤ} (hn : 0 ≤ n) : qGauss n (n-1) = qInt n := by
  by_cases hp : 0 < n
  · have h : (n-1).toNat = n.toNat-1 := by omega
    rw [qGauss,if_pos (by omega),h,qBinomial_codim_one n.toNat (by omega)]
    rfl
  · have h : n = 0 := by omega
    subst n
    simp [qGauss]

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Finite k] [Finite V]

def hyperplaneIntervalEquiv (S : Submodule k V) :
    {H : Submodule k V // Module.finrank k H = Module.finrank k V-1 ∧ S ≤ H} ≃
      IntermediateSubspace S ⊤ (Module.finrank k V-1) where
  toFun H := ⟨H.val,H.property.2,le_top,H.property.1⟩
  invFun H := ⟨H.val,H.property.2.2,H.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem hyperplanes (S : Submodule k V) (hV : 0 < Module.finrank k V) :
    (Nat.card {H : Submodule k V //
      Module.finrank k H = Module.finrank k V-1 ∧ S ≤ H} : ℤ) =
      eval (Nat.card k : ℤ) (qInt ((Module.finrank k V : ℤ)-Module.finrank k S)) := by
  rw [Nat.card_congr (hyperplaneIntervalEquiv S),subspaces S ⊤ _ le_top]
  simp only [finrank_top]
  have hdim := Submodule.finrank_le S
  have hcast : ((Module.finrank k V-1 : ℕ) : ℤ)-Module.finrank k S =
      ((Module.finrank k V : ℤ)-Module.finrank k S)-1 := by omega
  rw [hcast,qGauss_codim_one (by omega)]

/-- Choosing the smaller subspace leaves its actual upper interval. -/
def adjacentEquiv (lo up : Submodule k V) (m : ℕ) :
    AdjacentFlag lo up m ≃
      Σ I : IntermediateSubspace lo up m, IntermediateSubspace I.val up (m+1) where
  toFun f := ⟨⟨f.I,f.lower_le,f.middle_le.trans f.upper_le,f.I_dim⟩,
    ⟨f.K,f.middle_le,f.upper_le,f.K_dim⟩⟩
  invFun f := ⟨f.1.val,f.2.val,f.1.property.1,f.2.property.1,
    f.2.property.2.1,f.1.property.2.2,f.2.property.2.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by rcases f with ⟨⟨I,hI⟩,⟨K,hK⟩⟩; rfl

theorem adjacent (lo up : Submodule k V) (m : ℕ) (h : lo ≤ up) :
    (Nat.card (AdjacentFlag lo up m) : ℤ) = eval (Nat.card k : ℤ)
      (qGauss ((Module.finrank k up : ℤ)-Module.finrank k lo)
        ((m : ℤ)-Module.finrank k lo) * qInt ((Module.finrank k up : ℤ)-m)) := by
  classical
  letI : Fintype (IntermediateSubspace lo up m) := Fintype.ofFinite _
  rw [Nat.card_congr (adjacentEquiv lo up m),Nat.card_sigma,Nat.cast_sum]
  have hf (I : IntermediateSubspace lo up m) :
      (Nat.card (IntermediateSubspace I.val up (m+1)) : ℤ) =
        eval (Nat.card k : ℤ) (qInt ((Module.finrank k up : ℤ)-m)) := by
    rw [subspaces I.val up _ I.property.2.1,I.property.2.2]
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,qGauss_one]
  simp_rw [hf]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    subspaces lo up m h,eval_mul]

/-- The former input is now constructed from independent-frame counting
and actual quotient/flag equivalences. -/
def provedFiniteFlagCounts (k V : Type*) [Field k] [Finite k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Finite V] :
    GalleryCounting.FiniteFlagCounts k V where
  hyperplanes := hyperplanes
  subspaces := subspaces
  adjacent := adjacent

#print axioms provedFiniteFlagCounts
end Guralnick.FiniteFlagEnumeration
