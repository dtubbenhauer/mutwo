import Guralnick.WebMasks

/-!
# Absolute thin-position masks of cut-open web boundaries

A boundary determines its actual omitted affine simple generators by its
ordered partial sums and the specified cut. This construction does not
inspect the six-map word. The concrete local-stage calculations below
include every trivalent vertex and both changes of chart.
-/
namespace Guralnick.WebBoundary
open FiniteBlocks

/-- All boundary cuts, reduced modulo the fixed total number of positions. -/
def cuts {n : ℕ} (hn : 0<n) (b : Web.Boundary) : Finset (Fin n) :=
  ((b.packets.scanl (·+·) b.cut).map
    (fun s => (⟨s%n,Nat.mod_lt _ hn⟩ : Fin n))).toFinset

theorem initial_mem {n : ℕ} (hn : 0<n) (b : Web.Boundary) :
    (⟨b.cut%n,Nat.mod_lt _ hn⟩ : Fin n) ∈ cuts hn b := by
  unfold cuts
  simp only [List.mem_toFinset,List.mem_map]
  refine ⟨b.cut,?_,rfl⟩
  cases h : b.packets <;> simp [List.scanl]

/-- The actual finite-parabolic index of a displayed boundary. Validity of
packet labels and conservation is checked by the trace, separately. -/
def index {n : ℕ} (hn : 0<n) (b : Web.Boundary) : ParabolicWeb.Index n :=
  ⟨(cuts hn b)ᶜ,by
    intro h
    have hc : (⟨b.cut%n,Nat.mod_lt _ hn⟩ : Fin n) ∈ (cuts hn b)ᶜ :=
      h ▸ Finset.mem_univ _
    exact (Finset.mem_compl.mp hc) (initial_mem hn b)⟩

theorem index_composition {n : ℕ} (hn : 0<n) (A : FiniteBlocks.Composition n) :
    index hn (WebMasks.boundary A)=A.index := by rfl

namespace Family

/-- All local boundaries, including intermediate binary vertices and both
canonical recuts. These are independently displayed ordered packet lists. -/
def boundary (m : ℕ) (stage : Fin 15) : Web.Boundary :=
  [⟨0,[2*m+1]⟩,
   ⟨0,[m,m+1]⟩,
   ⟨0,[m,1,m]⟩,
   ⟨m+1,[m,m,1]⟩,
   ⟨m+1,[2*m,1]⟩,
   ⟨m+1,[m,m,1]⟩,
   ⟨m+1,[m,1,m-1,1]⟩,
   ⟨0,[1,m-1,1,m]⟩,
   ⟨0,[1,m-1,1,m-1,1]⟩,
   ⟨0,[1,m,m-1,1]⟩,
   ⟨0,[1,2*m-1,1]⟩,
   ⟨0,[1,m-1,m,1]⟩,
   ⟨0,[1,m-1,1,m-1,1]⟩,
   ⟨0,[m,1,m-1,1]⟩,
   ⟨0,[m,1,m]⟩].get stage

/-- Omitted positions, in absolute zero-based thin labels. -/
def omissions (m : ℕ) (stage : Fin 15) : List ℕ :=
  [[0],[0,m],[0,m,m+1],[0,m,m+1],[m,m+1],[0,m,m+1],
   [0,1,m,m+1],[0,1,m,m+1],[0,1,m,m+1,2*m],[0,1,m+1,2*m],
   [0,1,2*m],[0,1,m,2*m],[0,1,m,m+1,2*m],[0,m,m+1,2*m],
   [0,m,m+1]].get stage

set_option maxHeartbeats 1000000 in
theorem mem_index_iff {m : ℕ} (hm : 2≤m) (stage : Fin 15)
    (i : Fin (2*m+1)) :
    i ∈ (index (show 0<2*m+1 by omega) (boundary m stage)).val ↔
      i.val ∉ omissions m stage := by
  have h₁ : m<2*m+1 := by omega
  have h₂ : m+1<2*m+1 := by omega
  have h₃ : 1<2*m+1 := by omega
  have h₄ : 2*m<2*m+1 := by omega
  have h₅ : 1+(m-1)=m := by omega
  have h₆ : 1+(2*m-1)=2*m := by omega
  have h₇ : m+1+(m-1)=2*m := by omega
  have h₈ : (m+1+m)%(2*m+1)=0 := by rw [show m+1+m=2*m+1 by omega]; exact Nat.mod_self _
  have h₉ : (m+1+2*m)%(2*m+1)=m := by
    rw [show m+1+2*m=m+(2*m+1) by omega]
    simp [Nat.mod_eq_of_lt h₁]
  have h₁₀ : (m+1+2*m+1)%(2*m+1)=m+1 := by
    rw [show m+1+2*m+1=(m+1)+(2*m+1) by omega]
    simp [Nat.mod_eq_of_lt h₂]
  have a₁ : m+(m+1)=2*m+1 := by omega
  have a₂ : m+1+m+m=(2*m+1)+m := by omega
  have a₃ : m+1+m+m+1=(2*m+1)+(m+1) := by omega
  have a₄ : m+1+m+1=(2*m+1)+1 := by omega
  have a₅ : m+1+m+1+(m-1)=(2*m+1)+m := by omega
  have a₆ : m+1+m+1+(m-1)+1=(2*m+1)+(m+1) := by omega
  have a₇ : 1+m=m+1 := by omega
  have a₈ : 1+m+(m-1)=2*m := by omega
  have a₉ : 1+m+(m-1)+1=2*m+1 := by omega
  have a₁₀ : m+m=2*m := by omega
  have b₁ : (2*m+1+m+1)%(2*m+1)=m+1 := by
    rw [show 2*m+1+m+1=(2*m+1)+(m+1) by omega]
    simp [Nat.mod_eq_of_lt h₂]
  have b₂ : (2*m+1+1+(m-1))%(2*m+1)=m := by
    rw [show 2*m+1+1+(m-1)=(2*m+1)+m by omega]
    simp [Nat.mod_eq_of_lt h₁]
  have b₃ : (2*m+1+1+(m-1)+1)%(2*m+1)=m+1 := by
    rw [show 2*m+1+1+(m-1)+1=(2*m+1)+(m+1) by omega]
    simp [Nat.mod_eq_of_lt h₂]
  fin_cases stage <;>
    simp [index,cuts,boundary,omissions,List.scanl,List.get,
      h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,b₁,b₂,b₃,Nat.mod_eq_of_lt,
      Fin.ext_iff,-Fin.val_eq_zero_iff] <;> omega

end Family
end Guralnick.WebBoundary

namespace Guralnick.WebBoundary.Family

abbrev idx {m : ℕ} (hm : 2≤m) (stage : Fin 15) : ParabolicWeb.Index (2*m+1) :=
  index (show 0<2*m+1 by omega) (boundary m stage)

theorem idx_source {m : ℕ} (hm : 2≤m) : idx hm 0=ParabolicWeb.Family.source m := by
  change (FiniteBlocks.Family.source hm).index=ParabolicWeb.Family.source m
  exact FiniteBlocks.Family.source_index hm

theorem idx_output {m : ℕ} (hm : 2≤m) : idx hm 2=ParabolicWeb.Family.output m := by
  change (FiniteBlocks.Family.output hm).index=ParabolicWeb.Family.output m
  exact FiniteBlocks.Family.output_index hm

theorem idx_cyclic {m : ℕ} (hm : 2≤m) : idx hm 4=ParabolicWeb.Family.cyclic m := by
  change (WebMasks.cyclicDrawn hm).index=ParabolicWeb.Family.cyclic m
  exact WebMasks.cyclicDrawn_index hm

theorem idx_common {m : ℕ} (hm : 2≤m) : idx hm 8=ParabolicWeb.Family.common m := by
  change (FiniteBlocks.Family.common hm).index=ParabolicWeb.Family.common m
  exact FiniteBlocks.Family.common_index hm

theorem idx_middle {m : ℕ} (hm : 2≤m) : idx hm 10=ParabolicWeb.Family.middle m := by
  change (FiniteBlocks.Family.middle hm).index=ParabolicWeb.Family.middle m
  exact FiniteBlocks.Family.middle_index hm

theorem idx_common_again {m : ℕ} (hm : 2≤m) : idx hm 12=ParabolicWeb.Family.common m :=
  idx_common hm

theorem idx_output_again {m : ℕ} (hm : 2≤m) : idx hm 14=ParabolicWeb.Family.output m :=
  idx_output hm

/-- An independently checked omission-list inclusion gives the reverse
inclusion of the actual boundary parabolics. -/
theorem idx_subset {m : ℕ} (hm : 2≤m) (a b : Fin 15)
    (h : ∀ i, i∈omissions m a → i∈omissions m b) :
    (idx hm b).val⊆(idx hm a).val := by
  intro i hi
  rw [mem_index_iff hm] at hi ⊢
  exact fun hai => hi (h i.val hai)

theorem idx_eq {m : ℕ} (hm : 2≤m) (a b : Fin 15)
    (h : omissions m a=omissions m b) : idx hm a=idx hm b := by
  apply Subtype.ext
  ext i
  simp only [idx,mem_index_iff hm,h]

/-- Every binary operation has the exact refinement direction required
by its actual ordered packets. The recuts preserve absolute thin cuts. -/
theorem local_relations {m : ℕ} (hm : 2≤m) :
    (idx hm 1).val⊆(idx hm 0).val ∧
    (idx hm 2).val⊆(idx hm 1).val ∧
    idx hm 3=idx hm 2 ∧
    (idx hm 3).val⊆(idx hm 4).val ∧
    (idx hm 5).val⊆(idx hm 4).val ∧
    (idx hm 6).val⊆(idx hm 5).val ∧
    idx hm 7=idx hm 6 ∧
    (idx hm 8).val⊆(idx hm 7).val ∧
    (idx hm 8).val⊆(idx hm 9).val ∧
    (idx hm 9).val⊆(idx hm 10).val ∧
    (idx hm 11).val⊆(idx hm 10).val ∧
    (idx hm 12).val⊆(idx hm 11).val ∧
    (idx hm 12).val⊆(idx hm 13).val ∧
    (idx hm 13).val⊆(idx hm 14).val := by
  refine ⟨?_,?_,idx_eq hm 3 2 rfl,?_,?_,?_,idx_eq hm 7 6 rfl,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals apply idx_subset hm <;> intro i hi
  all_goals simp only [omissions,List.get,List.getElem_cons_zero,List.getElem_cons_succ,
    List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  all_goals tauto

end Guralnick.WebBoundary.Family
