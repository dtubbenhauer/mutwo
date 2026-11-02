import Guralnick.LatticeFlags

noncomputable section
set_option maxHeartbeats 1000000
namespace Guralnick.LatticeFlags
open LaurentLattice
variable {k : Type*} [Field k] {N : ℕ}

/-- A finite ordered lattice chain inside one period gives a partial flag.
The degree hypotheses ensure that the retained type labels are genuine. -/
def ofBounds {S : Finset (Fin N)} (nodes : {i // i ∈ S} → Lattice k N)
    (A Z : Lattice k N)
    (hAZ : Z.space ≤ LatticeGallery.expand (shift k N) A.space)
    (lower : ∀ i, A ≤ nodes i) (upper : ∀ i, nodes i ≤ Z)
    (ordered : ∀ i j, i.val ≤ j.val → nodes i ≤ nodes j)
    (degrees : ∀ i, degree k N (nodes i) = (i.val.val : ℤ)) : Flag k N S where
  node := nodes
  ordered := ordered
  degree_eq := degrees
  cyclic i j := by
    have hu : (nodes i).space ≤ Z.space := upper i
    have hl : A.space ≤ (nodes j).space := lower j
    exact hu.trans (hAZ.trans (Submodule.map_mono hl))

namespace Family
variable {m : ℕ} (hm : 2 ≤ m)

def threeNodes (A B C : Lattice k (2*m+1))
    (i : {i // i ∈ retained (ParabolicWeb.Family.output m)}) : Lattice k (2*m+1) :=
  if i.val.val = 0 then A else if i.val.val = m then B else C

/-- The retained chain of types 0,m,m+1. -/
def three (A B C : Lattice k (2*m+1)) (hAB : A ≤ B) (hBC : B ≤ C)
    (hCA : C.space ≤ LatticeGallery.expand (shift k (2*m+1)) A.space)
    (hA : degree k (2*m+1) A=0) (hB : degree k (2*m+1) B=m)
    (hC : degree k (2*m+1) C=m+1) :
    Flag k (2*m+1) (retained (ParabolicWeb.Family.output m)) := by
  have hm0 : m ≠ 0 := by omega
  refine ofBounds (threeNodes A B C) A C hCA ?_ ?_ ?_ ?_
  · intro i
    dsimp [threeNodes]
    split_ifs <;> first | exact le_rfl | exact hAB | exact hAB.trans hBC
  · intro i
    dsimp [threeNodes]
    split_ifs <;> first | exact hAB.trans hBC | exact hBC | exact le_rfl
  · intro i j hij
    change i.val.val ≤ j.val.val at hij
    obtain hi | hi | hi := (output_mem m i.val).mp i.property
    all_goals obtain hj | hj | hj := (output_mem m j.val).mp j.property
    all_goals simp only [threeNodes, hi, hj]
    all_goals split_ifs <;> first | exact le_rfl | exact hAB | exact hBC | exact hAB.trans hBC | contradiction | omega
  · intro i
    obtain hi | hi | hi := (output_mem m i.val).mp i.property
    all_goals simp [threeNodes, hi, hm0, hA, hB, hC]

def fiveNodes (A B C D E : Lattice k (2*m+1))
    (i : {i // i ∈ retained (ParabolicWeb.Family.common m)}) : Lattice k (2*m+1) :=
  if i.val.val = 0 then A else if i.val.val = 1 then B else
    if i.val.val = m then C else if i.val.val = m+1 then D else E

/-- The retained chain of types 0,1,m,m+1,2m. -/
def five (A B C D E : Lattice k (2*m+1))
    (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D) (hDE : D ≤ E)
    (hEA : E.space ≤ LatticeGallery.expand (shift k (2*m+1)) A.space)
    (hA : degree k (2*m+1) A=0) (hB : degree k (2*m+1) B=1)
    (hC : degree k (2*m+1) C=m) (hD : degree k (2*m+1) D=m+1)
    (hE : degree k (2*m+1) E=2*m) :
    Flag k (2*m+1) (retained (ParabolicWeb.Family.common m)) := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  have hAC := hAB.trans hBC
  have hAD := hAC.trans hCD
  have hAE := hAD.trans hDE
  have hBD := hBC.trans hCD
  have hBE := hBD.trans hDE
  have hCE := hCD.trans hDE
  refine ofBounds (fiveNodes A B C D E) A E hEA ?_ ?_ ?_ ?_
  · intro i
    dsimp [fiveNodes]
    split_ifs <;> first | assumption | exact le_rfl
  · intro i
    dsimp [fiveNodes]
    split_ifs <;> first | assumption | exact le_rfl
  · intro i j hij
    change i.val.val ≤ j.val.val at hij
    obtain hi | hi | hi | hi | hi := (common_mem m i.val).mp i.property
    all_goals obtain hj | hj | hj | hj | hj := (common_mem m j.val).mp j.property
    all_goals simp only [fiveNodes, hi, hj]
    all_goals split_ifs <;> first | exact le_rfl | assumption | contradiction | omega
  · intro i
    obtain hi | hi | hi | hi | hi := (common_mem m i.val).mp i.property
    all_goals simp only [fiveNodes, hi]
    all_goals split_ifs <;> simp_all <;> omega

end Family
end Guralnick.LatticeFlags
