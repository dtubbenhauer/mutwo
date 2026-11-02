import Guralnick.GalleryCounting
import Guralnick.GaussianReciprocity
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.BigOperators.Intervals

/-! # Counting actual subspaces by their ordered bases

The only counting theorem used here is mathlib's count of independent
ordered vectors. Partitioning those vectors by their actual span gives
the Grassmannian count; no Gaussian counting formula is an input.
-/
noncomputable section
open scoped BigOperators
open Polynomial
namespace Guralnick.FiniteFlagEnumeration

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

abbrev Grassmann (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ) :=
  {U : Submodule k V // Module.finrank k U = r}

abbrev Frame (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ) :=
  {s : Fin r → V // LinearIndependent k s}

def FrameIn (U : Submodule k V) (r : ℕ) :=
  {s : Frame k V r // ∀ i, s.val i ∈ U}

instance [Finite V] (U : Submodule k V) (r : ℕ) : Finite (FrameIn U r) := by
  unfold FrameIn
  infer_instance

def frameInEquiv (U : Submodule k V) (r : ℕ) : FrameIn U r ≃ Frame k U r where
  toFun s := ⟨fun i => ⟨s.val.val i,s.property i⟩,
    LinearIndependent.of_comp U.subtype s.val.property⟩
  invFun s := ⟨⟨fun i => (s.val i : V),
    s.property.map' U.subtype (Submodule.ker_subtype U)⟩,fun i => (s.val i).property⟩
  left_inv s := by rfl
  right_inv s := by rfl

theorem span_frame_eq [FiniteDimensional k V] {r : ℕ} (U : Grassmann k V r)
    (s : FrameIn U.val r) : Submodule.span k (Set.range s.val.val) = U.val := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact s.property i)
  · simpa [U.property] using finrank_span_eq_card s.val.property

/-- A frame determines its span, with no independently chosen label. -/
def framesBySpan [FiniteDimensional k V] (r : ℕ) :
    (Σ U : Grassmann k V r, FrameIn U.val r) ≃ Frame k V r :=
  Equiv.ofBijective (fun s => s.2.val) (by
    constructor
    · rintro ⟨⟨U,hU⟩,⟨s,hs⟩⟩ ⟨⟨W,hW⟩,⟨t,ht⟩⟩ he
      change s = t at he
      subst t
      have hUS := span_frame_eq ⟨U,hU⟩ ⟨s,hs⟩
      have hWS := span_frame_eq ⟨W,hW⟩ ⟨s,ht⟩
      have hUW : U = W := hUS.symm.trans hWS
      subst W
      rfl
    · intro s
      refine ⟨⟨⟨Submodule.span k (Set.range s.val),?_⟩,
        ⟨s,fun i => Submodule.subset_span ⟨i,rfl⟩⟩⟩,rfl⟩
      simpa using finrank_span_eq_card s.property)

def frameProduct (q : ℤ) (n r : ℕ) : ℤ := ∏ i ∈ Finset.range r, (q^n-q^i)
def factorialProduct (q : ℤ) (r : ℕ) : ℤ := ∏ i ∈ Finset.range r, (q^(i+1)-1)
def fallingProduct (q : ℤ) (n r : ℕ) : ℤ := ∏ i ∈ Finset.range r, (q^(n-i)-1)

theorem gaussian_factorial (q : ℤ) {n r : ℕ} (hr : r ≤ n) :
    eval q (Gaussian.qBinomial n r) * factorialProduct q r = fallingProduct q n r := by
  induction r with
  | zero => simp [factorialProduct,fallingProduct]
  | succ r ih =>
      have hratio := congrArg (eval q) (Gaussian.qBinomial_adjacent (by omega : r ≤ n))
      simp only [eval_mul,eval_sub,eval_one,eval_pow,eval_X] at hratio
      have hi := ih (by omega)
      simp only [factorialProduct,fallingProduct,Finset.prod_range_succ] at *
      linear_combination -(∏ i ∈ Finset.range r, (q^(i+1)-1)) * hratio +
        (q^(n-r)-1) * hi

theorem falling_self (q : ℤ) (r : ℕ) : fallingProduct q r r = factorialProduct q r := by
  unfold fallingProduct factorialProduct
  calc
    _ = ∏ i ∈ Finset.range r, (q^((r-1-i)+1)-1) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 2
      omega
    _ = _ := Finset.prod_range_reflect (fun i => q^(i+1)-1) r

theorem frameProduct_factor (q : ℤ) {n r : ℕ} (hr : r ≤ n) :
    frameProduct q n r = (∏ i ∈ Finset.range r, q^i) * fallingProduct q n r := by
  rw [frameProduct,fallingProduct,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have h : i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [mul_sub,mul_one,← pow_add,Nat.add_sub_of_le h]

theorem gaussian_frameProduct (q : ℤ) {n r : ℕ} (hr : r ≤ n) :
    eval q (Gaussian.qBinomial n r) * frameProduct q r r = frameProduct q n r := by
  rw [frameProduct_factor q (le_refl r),falling_self,frameProduct_factor q hr]
  rw [mul_left_comm,gaussian_factorial q hr]

theorem frameProduct_pos {q : ℤ} (hq : 1 < q) (r : ℕ) : 0 < frameProduct q r r := by
  apply Finset.prod_pos
  intro i hi
  apply sub_pos.mpr
  exact pow_lt_pow_right₀ hq (Finset.mem_range.mp hi)

theorem frame_cardinality [Finite k] [Finite V] (r : ℕ)
    (hr : r ≤ Module.finrank k V) :
    (Nat.card (Frame k V r) : ℤ) =
      frameProduct (Nat.card k) (Module.finrank k V) r := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  rw [card_linearIndependent hr,
    Fin.prod_univ_eq_prod_range (fun i : ℕ => Fintype.card k ^ Module.finrank k V -
      Fintype.card k ^ i) r]
  simp only [Nat.cast_prod,frameProduct,Nat.card_eq_fintype_card]
  apply Finset.prod_congr rfl
  intro i hi
  have hin : i ≤ Module.finrank k V := by have := Finset.mem_range.mp hi; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fintype.card_pos) hin)]
  simp only [Nat.cast_pow]

/-- Independent ordered vectors partition by the unique actual subspace
they span; every fiber has the number of ordered bases in dimension `r`. -/
theorem grassmann_card_mul [Finite k] [Finite V] [FiniteDimensional k V]
    (r : ℕ) (hr : r ≤ Module.finrank k V) :
    (Nat.card (Grassmann k V r) : ℤ) * frameProduct (Nat.card k) r r =
      frameProduct (Nat.card k) (Module.finrank k V) r := by
  classical
  letI : Fintype (Grassmann k V r) := Fintype.ofFinite _
  have hf (U : Grassmann k V r) :
      (Nat.card (FrameIn U.val r) : ℤ) = frameProduct (Nat.card k) r r := by
    rw [Nat.card_congr (frameInEquiv U.val r),frame_cardinality r (by rw [U.property])]
    rw [U.property]
  have hh := congrArg (fun t : ℕ => (t : ℤ)) (Nat.card_congr (framesBySpan (k := k) (V := V) r))
  change (Nat.card (Σ U : Grassmann k V r, FrameIn U.val r) : ℤ) =
    (Nat.card (Frame k V r) : ℤ) at hh
  rw [Nat.card_sigma,Nat.cast_sum,frame_cardinality r hr] at hh
  simp_rw [hf] at hh
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card] using hh

/-- The Gaussian formula for actual subspaces of any valid dimension. -/
theorem grassmann_cardinality [Finite k] [Finite V] [FiniteDimensional k V]
    (r : ℕ) (hr : r ≤ Module.finrank k V) :
    (Nat.card (Grassmann k V r) : ℤ) =
      eval (Nat.card k : ℤ) (Gaussian.qBinomial (Module.finrank k V) r) := by
  have hq : 1 < (Nat.card k : ℤ) := by
    letI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card (α := k))
  apply mul_right_cancel₀ (ne_of_gt (frameProduct_pos hq r))
  exact (grassmann_card_mul r hr).trans (gaussian_frameProduct _ hr).symm

end Guralnick.FiniteFlagEnumeration
