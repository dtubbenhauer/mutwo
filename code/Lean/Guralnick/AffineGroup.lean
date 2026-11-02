import Guralnick.Family
import Mathlib.GroupTheory.Coxeter.Length

/-!
# The affine group and the actual upper endpoint

Composition here is composition of the actual periodic bijections already
constructed in `Affine.lean`. The family endpoint is `u * w₀`, not a label
whose KL value has been prescribed. The cyclic Coxeter matrix is also
defined explicitly. Its identification with this permutation group is a
general literature theorem, not established by defining the matrix.
-/

namespace Guralnick.AffinePermutation
open scoped BigOperators

@[ext] theorem ext {n : ℕ} {u v : AffinePermutation n}
    (hr : u.residue = v.residue) (hw : u.winding = v.winding) : u = v := by
  cases u
  cases v
  cases hr
  cases hw
  rfl

def identity (n : ℕ) : AffinePermutation n where
  residue := Equiv.refl _
  winding := 0
  balanced := by simp

/-- `compose u v` applies `v` first, then `u`. -/
def compose {n : ℕ} (u v : AffinePermutation n) : AffinePermutation n where
  residue := u.residue * v.residue
  winding i := v.winding i + u.winding (v.residue i)
  balanced := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp, u.balanced, v.balanced]
    rfl

instance {n : ℕ} : Group (AffinePermutation n) where
  one := identity n
  mul := compose
  inv := inverse
  mul_assoc u v w := by
    apply ext
    · exact mul_assoc _ _ _
    · funext i
      change w.winding i + (v.winding (w.residue i) +
          u.winding (v.residue (w.residue i))) =
        (w.winding i + v.winding (w.residue i)) +
          u.winding (v.residue (w.residue i))
      omega
  one_mul u := by
    apply ext
    · exact one_mul _
    · funext i
      change u.winding i + 0 = u.winding i
      exact add_zero _
  mul_one u := by
    apply ext
    · exact mul_one _
    · funext i
      change 0 + u.winding i = u.winding i
      exact zero_add _
  inv_mul_cancel u := by
    apply ext
    · exact inv_mul_cancel _
    · funext i
      change u.winding i + -u.winding (u.residue.symm (u.residue i)) = 0
      simp

@[simp] theorem one_residue {n : ℕ} : (1 : AffinePermutation n).residue = 1 := rfl
@[simp] theorem one_winding {n : ℕ} : (1 : AffinePermutation n).winding = 0 := rfl
@[simp] theorem mul_residue {n : ℕ} (u v : AffinePermutation n) :
    (u * v).residue = u.residue * v.residue := rfl
@[simp] theorem mul_winding {n : ℕ} (u v : AffinePermutation n) (i : Fin n) :
    (u * v).winding i = v.winding i + u.winding (v.residue i) := rfl
theorem inv_eq_inverse {n : ℕ} (u : AffinePermutation n) : u⁻¹ = u.inverse := rfl

/-- The group operation agrees with composition on the actual periodic index set. -/
theorem equiv_mul {n : ℕ} (u v : AffinePermutation n) :
    (u * v).equiv = u.equiv * v.equiv := by
  apply Equiv.ext
  intro x
  simp [equiv, mul_winding, Equiv.Perm.mul_apply, add_assoc]

theorem equiv_one {n : ℕ} : (1 : AffinePermutation n).equiv = 1 := by
  apply Equiv.ext
  rintro ⟨i, q⟩
  simp [equiv]

theorem equiv_injective {n : ℕ} : Function.Injective (@equiv n) := by
  intro u v h
  apply ext
  · apply Equiv.ext
    intro i
    exact congrArg Prod.fst (Equiv.congr_fun h (i, 0))
  · funext i
    have hi := congrArg Prod.snd (Equiv.congr_fun h (i, 0))
    simpa [equiv] using hi

def equivHom (n : ℕ) : AffinePermutation n →* Equiv.Perm (Fin n × ℤ) where
  toFun := equiv
  map_one' := equiv_one
  map_mul' := equiv_mul

theorem onIntegers_mul {n : ℕ} [NeZero n] (u v : AffinePermutation n) :
    (u * v).onIntegers = u.onIntegers * v.onIntegers := by
  apply Equiv.ext
  intro z
  simp [onIntegers, equiv_mul, Equiv.Perm.mul_apply]

/-- The finite symmetric subgroup, with zero winding. -/
def finiteEmbedding (n : ℕ) : Equiv.Perm (Fin n) →* AffinePermutation n where
  toFun w := ⟨w, 0, by simp⟩
  map_one' := by apply ext <;> rfl
  map_mul' u v := by
    apply ext
    · rfl
    · funext i
      simp

/-- The reversal `[n,n-1,...,1]`, the finite longest element. -/
def longest (n : ℕ) : AffinePermutation n := finiteEmbedding n Fin.revPerm

@[simp] theorem longest_residue (n : ℕ) : (longest n).residue = Fin.revPerm := rfl
@[simp] theorem longest_winding (n : ℕ) : (longest n).winding = 0 := rfl

@[simp] theorem longest_sq (n : ℕ) : longest n * longest n = 1 := by
  apply ext
  · apply Equiv.ext
    intro i
    simp [Equiv.Perm.mul_apply]
  · funext i
    simp

@[simp] theorem longest_inv (n : ℕ) : (longest n)⁻¹ = longest n :=
  inv_eq_of_mul_eq_one_right (longest_sq n)

theorem mul_longest_entry {n : ℕ} (u : AffinePermutation n) (i : Fin n) :
    (u * longest n).entry i = u.entry i.rev := by
  simp [entry, Equiv.Perm.mul_apply]

end Guralnick.AffinePermutation

namespace Guralnick.Family

/-- The actual upper endpoint of the ordinary affine KL polynomial. -/
noncomputable def upper {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    AffinePermutation (2 * m + 1) :=
  affine hm hj hjm * AffinePermutation.longest (2 * m + 1)

theorem upper_inverse {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (upper hm hj hjm)⁻¹ =
      AffinePermutation.longest (2 * m + 1) * (affine hm hj hjm)⁻¹ := by
  simp [upper]

theorem upper_entry {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (i : Fin (2 * m + 1)) :
    (upper hm hj hjm).entry i = (affine hm hj hjm).entry i.rev :=
  AffinePermutation.mul_longest_entry _ _

end Guralnick.Family

namespace Guralnick.AffineCoxeter

/-- Cyclic affine type A adjacency; the intended range is `3 ≤ n`. -/
def Adjacent {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)

instance {n : ℕ} (i j : Fin n) : Decidable (Adjacent i j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem adjacent_symm {n : ℕ} (i j : Fin n) : Adjacent i j ↔ Adjacent j i := by
  unfold Adjacent
  tauto

/-- The genuine Coxeter matrix of affine type A for `n ≥ 3`. -/
def matrix (n : ℕ) : CoxeterMatrix (Fin n) where
  M i j := if i = j then 1 else if Adjacent i j then 3 else 2
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, eq_comm, adjacent_symm i j]
  diagonal i := by simp
  off_diagonal i j h := by simp [h]; split_ifs <;> decide

abbrev PresentedGroup (n : ℕ) := (matrix n).Group

/-- Actual Coxeter word length in the group given by the cyclic presentation. -/
noncomputable def presentedLength {n : ℕ} (w : PresentedGroup n) : ℕ :=
  (matrix n).toCoxeterSystem.length w

end Guralnick.AffineCoxeter
