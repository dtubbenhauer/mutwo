import Guralnick.LaurentLattice
import Guralnick.ParabolicWeb

/-!
# Partial periodic flags on actual Laurent-series lattices

A mask records retained type positions. Nodes are actual full lattices,
with their actual signed relative degree, cyclic containment, and boundary
order. Compatibility is equality at every retained common position.
-/

noncomputable section
namespace Guralnick.LatticeFlags
open LaurentLattice
variable (k : Type*) [Field k] (N : ℕ)

/-- The retained vertices are the complement of the parabolic generators. -/
def retained {N : ℕ} (I : ParabolicWeb.Index N) : Finset (Fin N) := I.valᶜ

structure Flag (S : Finset (Fin N)) where
  node : {i // i ∈ S} → Lattice k N
  ordered : ∀ i j, i.val ≤ j.val → node i ≤ node j
  cyclic : ∀ i j, (node i).space ≤
    LatticeGallery.expand (shift k N) (node j).space
  degree_eq : ∀ i, degree k N (node i) = (i.val.val : ℤ)

variable {k N}

@[ext] theorem Flag.ext {S : Finset (Fin N)} {F G : Flag k N S}
    (h : F.node = G.node) : F = G := by cases F; cases G; cases h; rfl

/-- Refinement/forgetting compatibility, for arbitrary masks. -/
def Compatible {S T : Finset (Fin N)} (F : Flag k N S) (G : Flag k N T) : Prop :=
  ∀ (i : Fin N) (hi : i ∈ S) (hj : i ∈ T), F.node ⟨i,hi⟩ = G.node ⟨i,hj⟩

theorem compatible_symm {S T : Finset (Fin N)} {F : Flag k N S} {G : Flag k N T}
    (h : Compatible F G) : Compatible G F := fun i hi hj => (h i hj hi).symm

/-- Forget exactly the vertices omitted by a smaller retained mask. -/
def Flag.restrict {S T : Finset (Fin N)} (F : Flag k N S) (h : T ⊆ S) :
    Flag k N T where
  node i := F.node ⟨i.val,h i.property⟩
  ordered i j hij := F.ordered _ _ hij
  cyclic i j := F.cyclic _ _
  degree_eq i := F.degree_eq _

theorem compatible_restrict {S T : Finset (Fin N)} (F : Flag k N S) (h : T ⊆ S) :
    Compatible F (F.restrict h) := by intro i hi hj; rfl

theorem restrict_eq_of_compatible {S T : Finset (Fin N)}
    (F : Flag k N S) (G : Flag k N T) (h : T ⊆ S) (hc : Compatible F G) :
    F.restrict h = G := by
  apply Flag.ext
  funext i
  exact hc i.val (h i.property) i.property

/-- Actual intermediate partial flags for any finite word of masks. -/
structure Gallery {steps : ℕ} (masks : Fin (steps+1) → Finset (Fin N))
    (source : Flag k N (masks 0)) (target : Flag k N (masks (Fin.last steps))) where
  flags : ∀ i, Flag k N (masks i)
  source_eq : flags 0 = source
  target_eq : flags (Fin.last steps) = target
  adjacent : ∀ i : Fin steps, Compatible (flags i.castSucc) (flags i.succ)

@[ext] theorem Gallery.ext {steps : ℕ}
    {masks : Fin (steps+1) → Finset (Fin N)}
    {source : Flag k N (masks 0)} {target : Flag k N (masks (Fin.last steps))}
    {g h : Gallery masks source target} (heq : g.flags = h.flags) : g = h := by
  cases g; cases h; cases heq; rfl

namespace Family
open ParabolicWeb

/-- Precisely the seven retained masks of the integral six-map composite. -/
def masks (m : ℕ) : Fin 7 → Finset (Fin (2*m+1)) :=
  ![retained (ParabolicWeb.Family.source m), retained (ParabolicWeb.Family.output m),
    retained (ParabolicWeb.Family.cyclic m), retained (ParabolicWeb.Family.common m),
    retained (ParabolicWeb.Family.middle m), retained (ParabolicWeb.Family.common m),
    retained (ParabolicWeb.Family.output m)]

theorem source_mem (m : ℕ) (i : Fin (2*m+1)) :
    i ∈ retained (ParabolicWeb.Family.source m) ↔ i.val = 0 := by
  simp [retained, ParabolicWeb.Family.source, ParabolicWeb.Family.sourceSet]

theorem output_mem (m : ℕ) (i : Fin (2*m+1)) :
    i ∈ retained (ParabolicWeb.Family.output m) ↔
      i.val = 0 ∨ i.val = m ∨ i.val = m+1 := by
  simp [retained, ParabolicWeb.Family.output, ParabolicWeb.Family.outputSet,
    ParabolicWeb.Family.sourceSet, ParabolicWeb.Family.cyclicSet]
  tauto

theorem cyclic_mem (m : ℕ) (i : Fin (2*m+1)) :
    i ∈ retained (ParabolicWeb.Family.cyclic m) ↔ i.val = m ∨ i.val = m+1 := by
  simp [retained, ParabolicWeb.Family.cyclic, ParabolicWeb.Family.cyclicSet]
  tauto

theorem middle_mem (m : ℕ) (i : Fin (2*m+1)) :
    i ∈ retained (ParabolicWeb.Family.middle m) ↔
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2*m := by
  simp [retained, ParabolicWeb.Family.middle, ParabolicWeb.Family.middleSet]
  tauto

theorem common_mem (m : ℕ) (i : Fin (2*m+1)) :
    i ∈ retained (ParabolicWeb.Family.common m) ↔
      i.val = 0 ∨ i.val = 1 ∨ i.val = m ∨ i.val = m+1 ∨ i.val = 2*m := by
  simp [retained, ParabolicWeb.Family.common, ParabolicWeb.Family.commonSet,
    ParabolicWeb.Family.cyclicSet, ParabolicWeb.Family.middleSet]
  tauto

end Family
end Guralnick.LatticeFlags
