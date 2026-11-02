import Guralnick.FiniteFlagEnumerationIntervals
import Mathlib.Order.Fin.Basic

/-!
# Completing a finite chain of actual vector subspaces

At each missing rank choose an intermediate subspace below the smallest
prescribed later subspace. The construction preserves all prescribed
subspaces and works over every field, without a counting hypothesis.
-/

noncomputable section
namespace Guralnick.FiniteFlagExtension
open FiniteFlagEnumeration GalleryCounting
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Every admissible rank occurs in an actual subspace interval. -/
theorem exists_intermediate (A B : Submodule k V) (hAB : A≤B) (r : ℕ)
    (hA : Module.finrank k A≤r) (hB : r≤Module.finrank k B) :
    ∃ U : Submodule k V, A≤U ∧ U≤B ∧ Module.finrank k U=r := by
  have hr : r-Module.finrank k A ≤ Module.finrank k (B ⧸ A.comap B.subtype) := by
    rw [interval_quotient_finrank A B hAB]
    omega
  obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank hr
  let U : Grassmann k (B ⧸ A.comap B.subtype) (r-Module.finrank k A) :=
    ⟨Submodule.span k (Set.range f),by simpa using finrank_span_eq_card hf⟩
  let Q := (intervalGrassmannEquiv A B hAB r hA).symm U
  exact ⟨Q.val,Q.property⟩

/-- At rank r, an extending subspace lies above every earlier prescribed
space and below every later one. -/
structure Stage (S : Finset (Submodule k V)) (r : ℕ) where
  space : Submodule k V
  rank_eq : Module.finrank k space=r
  below : ∀ U∈S, Module.finrank k U≤r → U≤space
  above : ∀ U∈S, r≤Module.finrank k U → space≤U

def zeroStage (S : Finset (Submodule k V)) : Stage S 0 where
  space := ⊥
  rank_eq := by simp
  below U _ h := by
    have he : (⊥ : Submodule k V)=U := Submodule.eq_of_le_of_finrank_eq bot_le (by rw [Nat.eq_zero_of_le_zero h]; simp)
    rw [←he]
  above _ _ _ := bot_le

/-- In a chain, rank comparison detects its order. -/
theorem chain_le_of_rank_le (S : Finset (Submodule k V))
    (hchain : ∀ A∈S, ∀ B∈S, A≤B ∨ B≤A)
    {A B : Submodule k V} (hA : A∈S) (hB : B∈S)
    (hr : Module.finrank k A≤Module.finrank k B) : A≤B := by
  rcases hchain A hA B hB with h|h
  · exact h
  · exact (Submodule.eq_of_le_of_finrank_le h hr).symm.le

/-- One actual rank can always be inserted while preserving the given chain. -/
theorem stage_step (S : Finset (Submodule k V)) (htop : (⊤ : Submodule k V)∈S)
    (hchain : ∀ A∈S, ∀ B∈S, A≤B ∨ B≤A) (r : ℕ)
    (hr : r<Module.finrank k V) (Q : Stage S r) :
    ∃ R : Stage S (r+1), Q.space≤R.space := by
  classical
  let T := S.filter (fun U : Submodule k V => r<Module.finrank k U)
  have hT : T.Nonempty := ⟨⊤,Finset.mem_filter.mpr ⟨htop,by simpa using hr⟩⟩
  obtain ⟨U,hU,hmin⟩ := Finset.exists_min_image T (fun U : Submodule k V => Module.finrank k U) hT
  have hUS := (Finset.mem_filter.mp hU).1
  have hrU := (Finset.mem_filter.mp hU).2
  obtain ⟨W,hQW,hWU,hW⟩ := exists_intermediate Q.space U
    (Q.above U hUS (le_of_lt hrU)) (r+1) (by rw [Q.rank_eq]; omega) (by omega)
  have hupper : ∀ P∈S, r+1≤Module.finrank k P → W≤P := by
    intro P hP hrP
    have hUP : U≤P := chain_le_of_rank_le S hchain hUS hP
      (hmin P (Finset.mem_filter.mpr ⟨hP,by omega⟩))
    exact hWU.trans hUP
  refine ⟨⟨W,hW,?_,hupper⟩,hQW⟩
  intro P hP hrP
  by_cases hp : Module.finrank k P≤r
  · exact (Q.below P hP hp).trans hQW
  · have he : Module.finrank k P=r+1 := by omega
    exact (Submodule.eq_of_le_of_finrank_eq (hupper P hP he.ge) (hW.trans he.symm)).symm.le

/-- Build the chain by successive, proven rank insertions. -/
def grow (S : Finset (Submodule k V)) (htop : (⊤ : Submodule k V)∈S)
    (hchain : ∀ A∈S, ∀ B∈S, A≤B ∨ B≤A) :
    (r : ℕ) → r≤Module.finrank k V → Stage S r
  | 0, _ => zeroStage S
  | r+1, hr => Classical.choose
      (stage_step S htop hchain r (by omega) (grow S htop hchain r (by omega)))

theorem grow_succ_le (S : Finset (Submodule k V)) (htop : (⊤ : Submodule k V)∈S)
    (hchain : ∀ A∈S, ∀ B∈S, A≤B ∨ B≤A) (r : ℕ)
    (hr : r<Module.finrank k V) :
    (grow S htop hchain r (le_of_lt hr)).space≤
      (grow S htop hchain (r+1) (by omega)).space :=
  Classical.choose_spec (stage_step S htop hchain r hr
    (grow S htop hchain r (le_of_lt hr)))

/-- A full flag containing every member of the given finite chain. -/
theorem exists_full_flag (S : Finset (Submodule k V)) (htop : (⊤ : Submodule k V)∈S)
    (hchain : ∀ A∈S, ∀ B∈S, A≤B ∨ B≤A) :
    ∃ f : Fin (Module.finrank k V+1) → Submodule k V,
      Monotone f ∧ (∀ i, Module.finrank k (f i)=i.val) ∧
      ∀ U∈S, f ⟨Module.finrank k U,by have := Submodule.finrank_le U; omega⟩=U := by
  let f : Fin (Module.finrank k V+1) → Submodule k V :=
    fun i => (grow S htop hchain i.val (by have := i.isLt; omega)).space
  refine ⟨f,?_,?_,?_⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact grow_succ_le S htop hchain i.val i.isLt
  · intro i
    exact (grow S htop hchain i.val (by have := i.isLt; omega)).rank_eq
  · intro U hU
    apply le_antisymm
    · exact (grow S htop hchain _ (Submodule.finrank_le U)).above U hU le_rfl
    · exact (grow S htop hchain _ (Submodule.finrank_le U)).below U hU le_rfl

#print axioms exists_intermediate
#print axioms exists_full_flag
end Guralnick.FiniteFlagExtension
