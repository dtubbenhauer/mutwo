import Guralnick.ParabolicFlagStabilizer
import Guralnick.LatticeTheory
import Guralnick.RelativeDimensions

/-! # Unrolling an actual cyclic lattice flag into one period -/
noncomputable section
namespace Guralnick.LatticeFlagExtension
open LaurentLattice LatticeGallery LatticeFlags ElementaryCoxeterCutLength
variable {k : Type} [Field k] {n : ℕ} [NeZero n]

def up (Λ : Lattice k n) : Lattice k n :=
  LatticeEquivariance.mapLattice (OrbitMatrix.scalarShift k n) Λ

def down (Λ : Lattice k n) : Lattice k n :=
  LatticeEquivariance.mapLattice (OrbitMatrix.scalarShift k n).symm Λ

@[simp] theorem up_space (Λ : Lattice k n) :
    (up Λ).space=expand (shift k n) Λ.space := rfl

@[simp] theorem up_down (Λ : Lattice k n) : up (down Λ)=Λ :=
  LatticeEquivariance.mapLattice_map_symm _ _

@[simp] theorem down_up (Λ : Lattice k n) : down (up Λ)=Λ :=
  LatticeEquivariance.mapLattice_symm_map _ _

theorem up_mono : Monotone (up (k:=k) (n:=n)) :=
  (LatticeEquivariance.orderEquiv (OrbitMatrix.scalarShift k n)).monotone

theorem down_mono : Monotone (down (k:=k) (n:=n)) :=
  (LatticeEquivariance.orderEquiv (OrbitMatrix.scalarShift k n).symm).monotone

theorem le_up (Λ : Lattice k n) : Λ ≤ up Λ := stable k n Λ

theorem up_degree (Λ : Lattice k n) : degree k n (up Λ)=degree k n Λ+n := by
  have h := dimension_degree Λ (up Λ) (le_up Λ)
  change (Module.finrank k (QuotientSpace Λ.space (expand (shift k n) Λ.space)) : ℤ)=_ at h
  rw [period_dimension] at h
  omega

theorem down_degree (Λ : Lattice k n) : degree k n (down Λ)=degree k n Λ-n := by
  have h := up_degree (down Λ)
  rw [up_down] at h
  omega

/-- Nodes before the retained base are raised by one actual Laurent period. -/
def raised {S : Finset (Fin n)} (F : Flag k n S) (b i : {i // i∈S}) : Lattice k n :=
  if i.val.val<b.val.val then up (F.node i) else F.node i

theorem base_le_raised {S : Finset (Fin n)} (F : Flag k n S) (b i : {i // i∈S}) :
    F.node b ≤ raised F b i := by
  unfold raised
  split_ifs with h
  · exact F.cyclic b i
  · exact F.ordered b i (by change b.val.val ≤ i.val.val; omega)

theorem raised_le_up_base {S : Finset (Fin n)} (F : Flag k n S) (b i : {i // i∈S}) :
    raised F b i ≤ up (F.node b) := by
  unfold raised
  split_ifs with h
  · exact up_mono (F.ordered i b (by change i.val.val ≤ b.val.val; omega))
  · exact F.cyclic i b

theorem raised_degree {S : Finset (Fin n)} (F : Flag k n S) (b i : {i // i∈S}) :
    degree k n (raised F b i)=(b.val.val : ℤ)+(cutRank b.val i.val).val := by
  rw [ElementaryCoxeterRotation.cutRank_int]
  unfold raised ElementaryCoxeterParabolic.cutPotential
  split_ifs with h
  · rw [up_degree,F.degree_eq]
    omega
  · rw [F.degree_eq]
    omega

/-- The raised nodes form a linear chain in their actual cut order. -/
theorem raised_order {S : Finset (Fin n)} (F : Flag k n S) (b i j : {i // i∈S})
    (h : cutRank b.val i.val ≤ cutRank b.val j.val) : raised F b i ≤ raised F b j := by
  have hi := i.val.isLt
  have hj := j.val.isLt
  have hb := b.val.isLt
  change (cutRank b.val i.val).val ≤ (cutRank b.val j.val).val at h
  simp only [cutRank] at h
  unfold raised
  split_ifs at h ⊢ with hi' hj'
  · exact up_mono (F.ordered i j (by change i.val.val ≤ j.val.val; omega))
  · omega
  · exact F.cyclic i j
  · exact F.ordered i j (by change i.val.val ≤ j.val.val; omega)

abbrev PeriodSpace {S : Finset (Fin n)} (F : Flag k n S) (b : {i // i∈S}) :=
  QuotientSpace (F.node b).space (up (F.node b)).space

instance periodSpace_finite {S : Finset (Fin n)} (F : Flag k n S) (b : {i // i∈S}) :
    FiniteDimensional k (PeriodSpace F b) := period_finite (F.node b)

theorem periodSpace_finrank {S : Finset (Fin n)} (F : Flag k n S) (b : {i // i∈S}) :
    Module.finrank k (PeriodSpace F b)=n := period_dimension (F.node b)

def quotientNode {S : Finset (Fin n)} (F : Flag k n S) (b i : {i // i∈S}) :
    Submodule k (PeriodSpace F b) :=
  quotientImage (F.node b).space (up (F.node b)).space (le_up _)
    (raised F b i).space (base_le_raised F b i) (raised_le_up_base F b i)

theorem quotientNode_rank {S : Finset (Fin n)} (F : Flag k n S) (b i : {i // i∈S}) :
    Module.finrank k (quotientNode F b i)=(cutRank b.val i.val).val := by
  rw [quotientNode,quotientImage_finrank]
  have h := dimension_degree (F.node b) (raised F b i) (base_le_raised F b i)
  rw [raised_degree,F.degree_eq] at h
  omega

theorem quotientNode_order {S : Finset (Fin n)} (F : Flag k n S) (b i j : {i // i∈S})
    (h : cutRank b.val i.val ≤ cutRank b.val j.val) : quotientNode F b i ≤ quotientNode F b j :=
  (quotientImage_le_iff _ _ _ _ _ _ _ _ _).mpr (raised_order F b i j h)

#print axioms quotientNode_rank
end Guralnick.LatticeFlagExtension
