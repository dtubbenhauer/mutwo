import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# The finite-vector-space gallery bijection

This is the original flag decomposition used in the four-case count of §3.
It uses actual subspaces with their inclusions and dimensions. It neither
assumes a cardinal formula nor identifies a gallery count with a Hecke
coefficient; those are distinct steps.
-/

namespace Guralnick.GalleryFlags
open scoped BigOperators

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A gallery in the endpoint quotient vector space, exactly with the
containments and dimensions in the manuscript. -/
structure Gallery (I₀ K₀ F F' : Submodule k V) (m N : ℕ) where
  L : Submodule k V
  I : Submodule k V
  K : Submodule k V
  H : Submodule k V
  line_dim : Module.finrank k L = 1
  I_dim : Module.finrank k I = m
  K_dim : Module.finrank k K = m+1
  hyperplane_dim : Module.finrank k H = N-1
  line_le_I : L ≤ I
  I_le_K : I ≤ K
  K_le_H : K ≤ H
  line_le_F : L ≤ F
  F'_le_H : F' ≤ H
  I₀_le_I : I₀ ≤ I
  K_le_K₀ : K ≤ K₀

/-- The line is chosen inside `F ∩ K₀`. -/
def LineChoice (K₀ F : Submodule k V) :=
  {L : Submodule k V // Module.finrank k L = 1 ∧ L ≤ F ⊓ K₀}

/-- The hyperplane is chosen to contain `F' + I₀`. -/
def HyperplaneChoice (I₀ F' : Submodule k V) (N : ℕ) :=
  {H : Submodule k V // Module.finrank k H = N-1 ∧ F' ⊔ I₀ ≤ H}

/-- After choosing the line and hyperplane, the remaining data are a flag
in the interval `[I₀+L, K₀∩H]`. The dimensions are still ambient dimensions. -/
structure IntervalFlag (I₀ K₀ L H : Submodule k V) (m : ℕ) where
  I : Submodule k V
  K : Submodule k V
  lower_le : I₀ ⊔ L ≤ I
  middle_le : I ≤ K
  upper_le : K ≤ K₀ ⊓ H
  I_dim : Module.finrank k I = m
  K_dim : Module.finrank k K = m+1

/-- The product expresses independence of the line and hyperplane choices.
The remaining flag is allowed to depend on both choices. -/
def Decomposed (I₀ K₀ F F' : Submodule k V) (m N : ℕ) :=
  Σ pair : LineChoice K₀ F × HyperplaneChoice I₀ F' N,
    IntervalFlag I₀ K₀ pair.1.val pair.2.val m

/-- The finite gallery and its line/hyperplane/interval description are
explicitly equivalent. No dimension count is postulated. -/
def galleryEquiv (I₀ K₀ F F' : Submodule k V) (m N : ℕ) :
    Gallery I₀ K₀ F F' m N ≃ Decomposed I₀ K₀ F F' m N where
  toFun g :=
    ⟨(⟨g.L, g.line_dim, le_inf g.line_le_F
        (g.line_le_I.trans (g.I_le_K.trans g.K_le_K₀))⟩,
      ⟨g.H, g.hyperplane_dim, sup_le g.F'_le_H
        (g.I₀_le_I.trans (g.I_le_K.trans g.K_le_H))⟩),
      ⟨g.I, g.K, sup_le g.I₀_le_I g.line_le_I, g.I_le_K,
        le_inf g.K_le_K₀ g.K_le_H, g.I_dim, g.K_dim⟩⟩
  invFun d :=
    { L := d.1.1.val
      I := d.2.I
      K := d.2.K
      H := d.1.2.val
      line_dim := d.1.1.property.1
      I_dim := d.2.I_dim
      K_dim := d.2.K_dim
      hyperplane_dim := d.1.2.property.1
      line_le_I := le_sup_right.trans d.2.lower_le
      I_le_K := d.2.middle_le
      K_le_H := d.2.upper_le.trans inf_le_right
      line_le_F := d.1.1.property.2.trans inf_le_left
      F'_le_H := le_sup_left.trans d.1.2.property.2
      I₀_le_I := le_sup_left.trans d.2.lower_le
      K_le_K₀ := d.2.upper_le.trans inf_le_left }
  left_inv g := by cases g; rfl
  right_inv d := by
    rcases d with ⟨⟨⟨L,hL⟩,⟨H,hH⟩⟩,⟨I,K,hlo,hmid,hup,hI,hK⟩⟩
    rfl

/-- Every pair of outer choices gives an ordered interval. There is no
additional incidence constraint relating the choices of `L` and `H`. -/
theorem choices_give_interval {I₀ K₀ F F' : Submodule k V} {N : ℕ}
    (h₀ : I₀ ≤ K₀) (hF : F ≤ F')
    (L : LineChoice K₀ F) (H : HyperplaneChoice I₀ F' N) :
    I₀ ⊔ L.val ≤ K₀ ⊓ H.val := by
  apply le_inf
  · exact sup_le h₀ (L.property.2.trans inf_le_right)
  · apply sup_le
    · exact le_sup_right.trans H.property.2
    · exact (L.property.2.trans inf_le_left).trans
        (hF.trans (le_sup_left.trans H.property.2))

noncomputable section

/-- The line case records actual containment in `I₀`. -/
def lineCase (I₀ L : Submodule k V) : ℕ := by
  classical
  exact if L ≤ I₀ then 0 else 1

/-- The hyperplane case records actual containment of `K₀`. -/
def hyperplaneCase (K₀ H : Submodule k V) : ℕ := by
  classical
  exact if K₀ ≤ H then 0 else 1

variable [FiniteDimensional k V]

/-- The lower end of the residual interval has dimension `r+epsilon`. -/
theorem lower_dimension (I₀ L : Submodule k V)
    (hL : Module.finrank k L = 1) :
    Module.finrank k (I₀ ⊔ L : Submodule k V) =
      Module.finrank k I₀ + lineCase I₀ L := by
  classical
  by_cases h : L ≤ I₀
  · simp only [lineCase, if_pos h, Nat.add_zero]
    exact congrArg (fun S : Submodule k V => Module.finrank k S) (sup_eq_left.mpr h)
  · have hinf : Module.finrank k (I₀ ⊓ L : Submodule k V) = 0 := by
      have hle := Submodule.finrank_mono (inf_le_right : I₀ ⊓ L ≤ L)
      by_contra hz
      have heqdim : Module.finrank k (I₀ ⊓ L : Submodule k V) =
          Module.finrank k L := by omega
      have heq := Submodule.eq_of_le_of_finrank_eq
        (inf_le_right : I₀ ⊓ L ≤ L) heqdim
      exact h (heq ▸ (inf_le_left : I₀ ⊓ L ≤ I₀))
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq I₀ L
    simpa [lineCase, h, hinf, hL] using hdim

/-- The upper end of the residual interval has dimension `dim K₀-eta`. -/
theorem upper_dimension (K₀ H : Submodule k V) (N : ℕ) (hN : 0 < N)
    (hV : Module.finrank k V = N) (hH : Module.finrank k H = N-1) :
    Module.finrank k (K₀ ⊓ H : Submodule k V) =
      Module.finrank k K₀ - hyperplaneCase K₀ H := by
  classical
  by_cases h : K₀ ≤ H
  · simp only [hyperplaneCase, if_pos h, Nat.sub_zero]
    exact congrArg (fun S : Submodule k V => Module.finrank k S) (inf_eq_left.mpr h)
  · have hsup : Module.finrank k (K₀ ⊔ H : Submodule k V) = N := by
      have hle := Submodule.finrank_mono (le_sup_right : H ≤ K₀ ⊔ H)
      have hbound := Submodule.finrank_le (K₀ ⊔ H)
      have hne : Module.finrank k (K₀ ⊔ H : Submodule k V) ≠
          Module.finrank k H := by
        intro heqdim
        have heq := Submodule.eq_of_le_of_finrank_eq
          (le_sup_right : H ≤ K₀ ⊔ H) heqdim.symm
        exact h (heq.symm ▸ (le_sup_left : K₀ ≤ K₀ ⊔ H))
      omega
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq K₀ H
    simp only [hyperplaneCase, if_neg h]
    omega

/-- The displayed four interval dimensions follow from the actual choices.
The intersection dimensions used to count outer choices are separate data. -/
theorem interval_dimensions {I₀ K₀ F F' : Submodule k V} {r N : ℕ}
    (hN : 0 < N) (hV : Module.finrank k V = N) (hI₀ : Module.finrank k I₀ = r)
    (hK₀ : Module.finrank k K₀ = N-r)
    (L : LineChoice K₀ F) (H : HyperplaneChoice I₀ F' N) :
    Module.finrank k (I₀ ⊔ L.val : Submodule k V) = r + lineCase I₀ L.val ∧
    Module.finrank k (K₀ ⊓ H.val : Submodule k V) =
      N-r-hyperplaneCase K₀ H.val := by
  constructor
  · simpa [hI₀] using lower_dimension I₀ L.val L.property.1
  · simpa [hK₀] using upper_dimension K₀ H.val N hN hV H.property.1

end

/-- Flags over a finite ambient space form a finite type. -/
instance finiteIntervalFlag [Finite V] (I₀ K₀ L H : Submodule k V) (m : ℕ) :
    Finite (IntervalFlag I₀ K₀ L H m) := by
  classical
  letI : Finite (Submodule k V) := Finite.of_injective
    (fun S : Submodule k V => (S : Set V)) SetLike.coe_injective
  apply Finite.of_injective (fun g : IntervalFlag I₀ K₀ L H m => (g.I,g.K))
  intro x y h
  cases x
  cases y
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩
  rfl

instance finiteLineChoice [Finite (Submodule k V)] (K₀ F : Submodule k V) :
    Finite (LineChoice K₀ F) := by
  unfold LineChoice
  infer_instance

instance finiteHyperplaneChoice [Finite (Submodule k V)]
    (I₀ F' : Submodule k V) (N : ℕ) :
    Finite (HyperplaneChoice I₀ F' N) := by
  unfold HyperplaneChoice
  infer_instance

/-- Cardinality of the actual gallery set, before substituting any Gaussian
formula. The sum is over independent line and hyperplane choices. -/
theorem gallery_cardinality [Finite V] (I₀ K₀ F F' : Submodule k V) (m N : ℕ) :
    Nat.card (Gallery I₀ K₀ F F' m N) =
      letI : Finite (Submodule k V) := Finite.of_injective
        (fun S : Submodule k V => (S : Set V)) SetLike.coe_injective
      letI : Fintype (LineChoice K₀ F) := Fintype.ofFinite _
      letI : Fintype (HyperplaneChoice I₀ F' N) := Fintype.ofFinite _
      ∑ L : LineChoice K₀ F, ∑ H : HyperplaneChoice I₀ F' N,
        Nat.card (IntervalFlag I₀ K₀ L.val H.val m) := by
  classical
  letI : Finite (Submodule k V) := Finite.of_injective
    (fun S : Submodule k V => (S : Set V)) SetLike.coe_injective
  letI : Fintype (LineChoice K₀ F) := Fintype.ofFinite _
  letI : Fintype (HyperplaneChoice I₀ F' N) := Fintype.ofFinite _
  rw [Nat.card_congr (galleryEquiv I₀ K₀ F F' m N)]
  unfold Decomposed
  rw [Nat.card_sigma, Fintype.sum_prod_type]

end Guralnick.GalleryFlags
