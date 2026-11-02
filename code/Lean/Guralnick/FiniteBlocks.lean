import Guralnick.ParabolicWeb
import Guralnick.CanonicalChains
import Guralnick.KLFamily

/-!
# Cyclic block lengths and the six-map normalization

A positive cyclic composition specifies the actual omitted generators by
its partial sums. The general finite-parabolic type-A longest-length formula
is an explicit literature input. All five special compositions and the
normalization cost of the six-map word are calculated here.
-/

noncomputable section
namespace Guralnick.FiniteBlocks
open scoped BigOperators

structure Composition (n : ℕ) where
  packets : List ℕ
  positive : ∀ a ∈ packets, 0 < a
  total : packets.sum = n
  cut : Fin n

namespace Composition
variable {n : ℕ}

def cuts (A : Composition n) : Finset (Fin n) :=
  ((A.packets.scanl (· + ·) A.cut.val).map
    (fun s => (⟨s % n, Nat.mod_lt _ (Fin.pos A.cut)⟩ : Fin n))).toFinset

theorem cut_mem (A : Composition n) : A.cut ∈ A.cuts := by
  unfold cuts
  simp only [List.mem_toFinset, List.mem_map]
  refine ⟨A.cut.val, ?_, ?_⟩
  · cases h : A.packets <;> simp [List.scanl]
  · apply Fin.ext
    exact Nat.mod_eq_of_lt A.cut.isLt

def index (A : Composition n) : ParabolicWeb.Index n :=
  ⟨A.cutsᶜ, by
    intro h
    have hc : A.cut ∈ A.cutsᶜ := h ▸ Finset.mem_univ _
    exact (Finset.mem_compl.mp hc) A.cut_mem⟩

def twiceLongestLength (A : Composition n) : ℤ :=
  (A.packets.map fun (a : ℕ) => (a : ℤ) * ((a : ℤ) - 1)).sum

end Composition

/-- The general type-A block formula, for every positive cyclic composition.
It is the finite symmetric-group longest length formula applied to the
connected components of the proper affine-A parabolic diagram. -/
def BlockLengthInput {n : ℕ} {c : Hecke.WindowCoxeter n}
    (D : ∀ I : ParabolicWeb.Index n, ParabolicWeb.LongestData c I) : Prop :=
  ∀ A : Composition n,
    2 * (c.system.length (D A.index).longest.val : ℤ) = A.twiceLongestLength

/-- The ordinary finite symmetric parabolic has the actual reversal as its
longest element. This is a general finite type-A identification, not a
special assertion about any of the manuscript's affine endpoints. -/
def StandardFiniteLongestInput {n : ℕ} {c : Hecke.WindowCoxeter n}
    (D : ∀ I : ParabolicWeb.Index n, ParabolicWeb.LongestData c I) : Prop :=
  ∀ hn : 0 < n, (D (CanonicalChains.source hn)).longest.val = AffinePermutation.longest n

namespace Family
open ParabolicWeb

def source {m : ℕ} (hm : 2 ≤ m) : Composition (2*m+1) where
  packets := [2*m+1]
  positive := by simp
  total := by simp
  cut := ⟨0, by omega⟩

def output {m : ℕ} (hm : 2 ≤ m) : Composition (2*m+1) where
  packets := [m,1,m]
  positive := by simp; omega
  total := by simp; omega
  cut := ⟨0, by omega⟩

def cyclic {m : ℕ} (hm : 2 ≤ m) : Composition (2*m+1) where
  packets := [1,2*m]
  positive := by simp; omega
  total := by simp; omega
  cut := ⟨m, by omega⟩

def middle {m : ℕ} (hm : 2 ≤ m) : Composition (2*m+1) where
  packets := [1,2*m-1,1]
  positive := by simp; omega
  total := by simp; omega
  cut := ⟨0, by omega⟩

def common {m : ℕ} (hm : 2 ≤ m) : Composition (2*m+1) where
  packets := [1,m-1,1,m-1,1]
  positive := by simp; omega
  total := by simp; omega
  cut := ⟨0, by omega⟩

theorem source_index {m : ℕ} (hm : 2 ≤ m) :
    (source hm).index = ParabolicWeb.Family.source m := by
  apply Subtype.ext
  ext i
  simp [Composition.index, Composition.cuts, source, List.scanl,
    ParabolicWeb.Family.source, ParabolicWeb.Family.sourceSet, Fin.ext_iff,
    -Fin.val_eq_zero_iff]

theorem output_index {m : ℕ} (hm : 2 ≤ m) :
    (output hm).index = ParabolicWeb.Family.output m := by
  have h₁ : m < 2*m+1 := by omega
  have h₂ : m+1 < 2*m+1 := by omega
  have h₃ : m+1+m = 2*m+1 := by omega
  apply Subtype.ext
  ext i
  simp [Composition.index, Composition.cuts, output, List.scanl, h₁, h₂, h₃,
    Nat.mod_eq_of_lt, ParabolicWeb.Family.output, ParabolicWeb.Family.outputSet,
    ParabolicWeb.Family.sourceSet, ParabolicWeb.Family.cyclicSet, Fin.ext_iff,
    -Fin.val_eq_zero_iff]
  tauto

theorem cyclic_index {m : ℕ} (hm : 2 ≤ m) :
    (cyclic hm).index = ParabolicWeb.Family.cyclic m := by
  have h₁ : m < 2*m+1 := by omega
  have h₂ : m+1 < 2*m+1 := by omega
  have h₃ : (m+1+2*m) % (2*m+1) = m := by
    rw [show m+1+2*m = m+(2*m+1) by omega]
    simp [Nat.add_mod, Nat.mod_eq_of_lt h₁]
  apply Subtype.ext
  ext i
  simp [Composition.index, Composition.cuts, cyclic, List.scanl, h₁, h₂, h₃,
    Nat.mod_eq_of_lt, ParabolicWeb.Family.cyclic, ParabolicWeb.Family.cyclicSet,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  tauto

theorem middle_index {m : ℕ} (hm : 2 ≤ m) :
    (middle hm).index = ParabolicWeb.Family.middle m := by
  have h₁ : 1 < 2*m+1 := by omega
  have h₂ : 1+(2*m-1) = 2*m := by omega
  have h₃ : 2*m < 2*m+1 := by omega
  apply Subtype.ext
  ext i
  simp [Composition.index, Composition.cuts, middle, List.scanl, h₁, h₂, h₃,
    Nat.mod_eq_of_lt, ParabolicWeb.Family.middle, ParabolicWeb.Family.middleSet,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  tauto

theorem common_index {m : ℕ} (hm : 2 ≤ m) :
    (common hm).index = ParabolicWeb.Family.common m := by
  have h₁ : 1 < 2*m+1 := by omega
  have h₂ : 1+(m-1) = m := by omega
  have h₃ : m < 2*m+1 := by omega
  have h₄ : m+1 < 2*m+1 := by omega
  have h₅ : m+1+(m-1) = 2*m := by omega
  have h₆ : 2*m < 2*m+1 := by omega
  apply Subtype.ext
  ext i
  simp [Composition.index, Composition.cuts, common, List.scanl,
    h₁, h₂, h₃, h₄, h₅, h₆, Nat.mod_eq_of_lt,
    ParabolicWeb.Family.common, ParabolicWeb.Family.commonSet,
    ParabolicWeb.Family.cyclicSet, ParabolicWeb.Family.middleSet, Fin.ext_iff,
    -Fin.val_eq_zero_iff]
  tauto

/-- The three merge costs telescope. Inclusions have cost zero. -/
def cost {m : ℕ} {c : Hecke.WindowCoxeter (2*m+1)}
    (D : ∀ I : Index (2*m+1), LongestData c I) : ℤ :=
  ((c.system.length (D (ParabolicWeb.Family.cyclic m)).longest.val : ℤ) -
    c.system.length (D (ParabolicWeb.Family.output m)).longest.val) +
  ((c.system.length (D (ParabolicWeb.Family.middle m)).longest.val : ℤ) -
    c.system.length (D (ParabolicWeb.Family.common m)).longest.val) +
  ((c.system.length (D (ParabolicWeb.Family.output m)).longest.val : ℤ) -
    c.system.length (D (ParabolicWeb.Family.common m)).longest.val)

theorem cost_eq {m : ℕ} (hm : 2 ≤ m) {c : Hecke.WindowCoxeter (2*m+1)}
    (D : ∀ I : Index (2*m+1), LongestData c I) (h : BlockLengthInput D) :
    cost D = 2*(m : ℤ)^2 + 2*m - 3 := by
  have hJ := h (cyclic hm)
  have hK := h (middle hm)
  have hL := h (common hm)
  rw [cyclic_index] at hJ
  rw [middle_index] at hK
  rw [common_index] at hL
  simp only [Composition.twiceLongestLength, cyclic, middle, common, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_one,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ 2*m by omega),
    Nat.cast_sub (show 1 ≤ m by omega)] at hJ hK hL
  unfold cost
  nlinarith

theorem source_eq_standard (m : ℕ) :
    ParabolicWeb.Family.source m = CanonicalChains.source (show 0 < 2*m+1 by omega) := by
  apply Subtype.ext
  ext i
  simp [ParabolicWeb.Family.source, ParabolicWeb.Family.sourceSet,
    CanonicalChains.source, CanonicalChains.omitNode, Fin.ext_iff, -Fin.val_eq_zero_iff]

theorem main_weight {m : ℕ} {c : Hecke.WindowCoxeter (2*m+1)}
    (D : ∀ I : Index (2*m+1), LongestData c I) :
    CanonicalChains.Chain.weight D (CanonicalChains.mainChain m) =
      (c.system.length (D (ParabolicWeb.Family.source m)).longest.val : ℤ) + cost D := by
  simp only [CanonicalChains.mainChain, CanonicalChains.Chain.weight]
  rw [CanonicalChains.main_meet_source m, CanonicalChains.main_meet_cyclic m,
    CanonicalChains.main_meet_middle m]
  unfold cost
  ring

/-- The exact exponent supplied to normalized convolution, now using the
proved family length gap and calculated cyclic composition cost. -/
theorem main_family_exponent {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    {c : Hecke.WindowCoxeter (2*m+1)}
    (D : ∀ I : Index (2*m+1), LongestData c I)
    (hblocks : BlockLengthInput D) (hsource : StandardFiniteLongestInput D) :
    CanonicalChains.Chain.weight D (CanonicalChains.mainChain m) -
      c.system.length (Guralnick.Family.upper hm hj hjm) =
        (2*(m : ℤ)^2+2*m-3) - gapFormula m j := by
  rw [main_weight, cost_eq hm D hblocks, source_eq_standard, hsource]
  have h := Hecke.family_length_gap hm hj hjm c
  omega

end Family
end Guralnick.FiniteBlocks
