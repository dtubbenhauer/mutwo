import Guralnick.Web
import Guralnick.FiniteBlocks
import Guralnick.LatticeFlags

/-!
# From the drawn ribbon boundaries to the actual parabolic masks

The graph's ordered packet sizes and cyclic cut determine the omitted
simple generators. This file checks all seven stages against the parabolics
used by the integral module maps and the lattice galleries. In particular,
the seam stage retains positions m and m+1, despite being drawn with its
cyclic boundary starting at m+1. No winding is discarded.
-/

namespace Guralnick.WebMasks
open FiniteBlocks

def boundary {n : ℕ} (A : FiniteBlocks.Composition n) : Web.Boundary :=
  ⟨A.cut.val, A.packets⟩

def cyclicDrawn {m : ℕ} (hm : 2 ≤ m) : FiniteBlocks.Composition (2*m+1) where
  packets := [2*m,1]
  positive := by simp; omega
  total := by simp
  cut := ⟨m+1, by omega⟩

theorem cyclicDrawn_index {m : ℕ} (hm : 2 ≤ m) :
    (cyclicDrawn hm).index = ParabolicWeb.Family.cyclic m := by
  have h₁ : m < 2*m+1 := by omega
  have h₂ : m+1 < 2*m+1 := by omega
  have h₃ : (m+1+2*m) % (2*m+1) = m := by
    rw [show m+1+2*m = m+(2*m+1) by omega]
    simp [Nat.mod_eq_of_lt h₁]
  have h₄ : (m+1+2*m+1) % (2*m+1) = m+1 := by
    rw [show m+1+2*m+1 = (m+1)+(2*m+1) by omega]
    simp [Nat.mod_eq_of_lt h₂]
  apply Subtype.ext
  ext i
  simp [FiniteBlocks.Composition.index, FiniteBlocks.Composition.cuts, cyclicDrawn, List.scanl,
    h₁, h₂, h₃, h₄, Nat.mod_eq_of_lt,
    ParabolicWeb.Family.cyclic, ParabolicWeb.Family.cyclicSet,
    Fin.ext_iff, -Fin.val_eq_zero_iff]

def stages {m : ℕ} (hm : 2 ≤ m) : List (FiniteBlocks.Composition (2*m+1)) :=
  [FiniteBlocks.Family.source hm, FiniteBlocks.Family.output hm, cyclicDrawn hm,
    FiniteBlocks.Family.common hm, FiniteBlocks.Family.middle hm,
    FiniteBlocks.Family.common hm, FiniteBlocks.Family.output hm]

theorem stage_boundaries {m : ℕ} (hm : 2 ≤ m) :
    (stages hm).map boundary = (Web.family m).boundaries := by
  rw [Web.family_boundaries m hm]
  rfl

theorem stage_parabolics {m : ℕ} (hm : 2 ≤ m) :
    (stages hm).map FiniteBlocks.Composition.index =
      [ParabolicWeb.Family.source m, ParabolicWeb.Family.output m,
       ParabolicWeb.Family.cyclic m, ParabolicWeb.Family.common m,
       ParabolicWeb.Family.middle m, ParabolicWeb.Family.common m,
       ParabolicWeb.Family.output m] := by
  simp only [stages, List.map_cons, List.map_nil, FiniteBlocks.Family.source_index,
    FiniteBlocks.Family.output_index, cyclicDrawn_index, FiniteBlocks.Family.common_index,
    FiniteBlocks.Family.middle_index]

/-- The exact omitted-generator masks of the drawn graph are the exact
retained-lattice masks used in the six-map gallery definition. -/
theorem stage_masks {m : ℕ} (hm : 2 ≤ m) :
    (stages hm).map FiniteBlocks.Composition.cuts = List.ofFn (LatticeFlags.Family.masks m) := by
  have h : (stages hm).map FiniteBlocks.Composition.cuts =
      ((stages hm).map FiniteBlocks.Composition.index).map LatticeFlags.retained := by
    simp only [List.map_map, Function.comp_def, LatticeFlags.retained,
      FiniteBlocks.Composition.index, compl_compl]
  rw [h, stage_parabolics]
  simp [LatticeFlags.Family.masks, List.ofFn_succ]

end Guralnick.WebMasks
