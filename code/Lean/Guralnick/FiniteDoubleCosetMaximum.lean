import Guralnick.CanonicalSchur

/-! # Maximal representatives in actual finite double cosets

A maximum is chosen in the finite product of the two actual parabolic
subgroups. Multiplication by a required simple reflection remains in that
product; its length changes by one, so every maximum has the required
left and right descents. No orbit-classification theorem is used.
-/
noncomputable section
namespace Guralnick.FiniteDoubleCosetMaximum
open Hecke ParabolicWeb CanonicalSchur
variable {n : ℕ} (c : WindowCoxeter n) (I J : Index n)

theorem doubleMaximal_of_bound (w : AffinePermutation n)
    (h : ∀ (a : subgroup c I) (b : subgroup c J),
      c.system.length (a.val*w*b.val) ≤ c.system.length w) : DoubleMaximal c I J w := by
  constructor
  · intro i hi
    have hs : c.system.simple i∈subgroup c I := Subgroup.subset_closure ⟨i,hi,rfl⟩
    have hh := h ⟨c.system.simple i,hs⟩ 1
    simp only [Subgroup.coe_one,mul_one] at hh
    exact lt_of_le_of_ne hh (c.system.length_simple_mul_ne _ _)
  · intro j hj
    have hs : c.system.simple j∈subgroup c J := Subgroup.subset_closure ⟨j,hj,rfl⟩
    have hh := h 1 ⟨c.system.simple j,hs⟩
    simp only [Subgroup.coe_one,one_mul] at hh
    exact lt_of_le_of_ne hh (c.system.length_mul_simple_ne _ _)

theorem exists_maximum (DI : LongestData c I) (DJ : LongestData c J)
    (w : AffinePermutation n) :
    ∃ z : AffinePermutation n,
      (∃ (a : subgroup c I) (b : subgroup c J), a.val*w*b.val=z) ∧
      DoubleMaximal c I J z ∧
      ∀ (a : subgroup c I) (b : subgroup c J),
        c.system.length (a.val*w*b.val) ≤ c.system.length z := by
  classical
  letI : Finite (subgroup c I) := DI.finite
  letI : Finite (subgroup c J) := DJ.finite
  letI := Fintype.ofFinite (subgroup c I)
  letI := Fintype.ofFinite (subgroup c J)
  obtain ⟨p,_,hp⟩ := Finset.exists_max_image
    (Finset.univ : Finset (subgroup c I × subgroup c J))
    (fun p => c.system.length (p.1.val*w*p.2.val)) Finset.univ_nonempty
  refine ⟨p.1.val*w*p.2.val,⟨p.1,p.2,rfl⟩,?_,?_⟩
  · apply doubleMaximal_of_bound
    intro a b
    have h := hp (a*p.1,p.2*b) (Finset.mem_univ _)
    simpa only [Subgroup.coe_mul,mul_assoc] using h
  · intro a b
    exact hp (a,b) (Finset.mem_univ _)

#print axioms doubleMaximal_of_bound
#print axioms exists_maximum
end Guralnick.FiniteDoubleCosetMaximum
