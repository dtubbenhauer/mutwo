import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Periodic affine permutations and independently checkable windows

The underlying periodic ordered set is `Fin n × ℤ`: `(i,q)` denotes the
integer `i+1+n*q`. This is an actual bijection with integral winding, not
a name for a table of lengths. `balanced` imposes the affine (rather than
extended affine) condition. Identification of the inversion count below
with Coxeter length is a separate, currently unformalized theorem.
-/
namespace Guralnick
open scoped BigOperators

structure AffinePermutation (n : ℕ) where
  residue : Equiv.Perm (Fin n)
  winding : Fin n → ℤ
  balanced : ∑ i, winding i = 0

namespace AffinePermutation

/-- The periodic index set is the integers, with one-based residues. -/
def integerIndex (n : ℕ) [NeZero n] : (Fin n × ℤ) ≃ ℤ :=
  (Equiv.prodComm (Fin n) ℤ).trans ((Int.divModEquiv n).symm.trans (Equiv.addRight 1))

def equiv {n : ℕ} (w : AffinePermutation n) : (Fin n × ℤ) ≃ (Fin n × ℤ) where
  toFun x := (w.residue x.1, x.2 + w.winding x.1)
  invFun x := (w.residue.symm x.1, x.2 - w.winding (w.residue.symm x.1))
  left_inv x := by simp
  right_inv x := by simp

def periodShift {n : ℕ} (x : Fin n × ℤ) : Fin n × ℤ := (x.1, x.2 + 1)

/-- The corresponding actual bijection of `ℤ`. -/
def onIntegers {n : ℕ} [NeZero n] (w : AffinePermutation n) : ℤ ≃ ℤ :=
  (integerIndex n).symm.trans (w.equiv.trans (integerIndex n))

theorem integerIndex_apply {n : ℕ} [NeZero n] (x : Fin n × ℤ) :
    integerIndex n x = (x.1.val : ℤ) + 1 + n*x.2 := by
  simp [integerIndex, Int.divModEquiv]
  ring

theorem periodic {n : ℕ} (w : AffinePermutation n) (x : Fin n × ℤ) :
    w.equiv (periodShift x) = periodShift (w.equiv x) := by
  simp [equiv, periodShift, add_assoc, add_comm, add_left_comm]

theorem onIntegers_index {n : ℕ} [NeZero n] (w : AffinePermutation n)
    (x : Fin n × ℤ) : w.onIntegers (integerIndex n x) = integerIndex n (w.equiv x) := by
  simp [onIntegers]

theorem integerIndex_shift {n : ℕ} [NeZero n] (x : Fin n × ℤ) :
    integerIndex n (periodShift x) = integerIndex n x + n := by
  simp only [integerIndex_apply, periodShift]
  ring

/-- The defining periodicity equation in the usual integer model. -/
theorem onIntegers_periodic {n : ℕ} [NeZero n] (w : AffinePermutation n) (z : ℤ) :
    w.onIntegers (z+n) = w.onIntegers z + n := by
  obtain ⟨x, rfl⟩ := (integerIndex n).surjective z
  rw [← integerIndex_shift, onIntegers_index, periodic, integerIndex_shift, onIntegers_index]

def entry {n : ℕ} (w : AffinePermutation n) (i : Fin n) : ℤ :=
  (w.residue i).val + 1 + n * w.winding i

def window {n : ℕ} (w : AffinePermutation n) : List ℤ := List.ofFn w.entry

theorem sum_entry {n : ℕ} (w : AffinePermutation n) :
    ∑ i, w.entry i = ∑ i : Fin n, ((i.val : ℤ) + 1) := by
  simp only [entry, Finset.sum_add_distrib, ← Finset.mul_sum, w.balanced, mul_zero,
    add_zero]
  congr 1
  exact Equiv.sum_comp w.residue (fun i : Fin n => (i.val : ℤ))

def inverse {n : ℕ} (w : AffinePermutation n) : AffinePermutation n where
  residue := w.residue.symm
  winding i := -w.winding (w.residue.symm i)
  balanced := by rw [Finset.sum_neg_distrib, Equiv.sum_comp, w.balanced, neg_zero]

/-- The positive `p`-dot action on the zero weight, in arbitrary rho coordinates.
The shift attached to an output residue is obtained from its input preimage. -/
def dotZero {n : ℕ} (w : AffinePermutation n) (p : ℤ) (rho : Fin n → ℤ)
    (i : Fin n) : ℤ :=
  p * w.winding (w.residue.symm i) + rho (w.residue.symm i) - rho i

theorem dotZero_sum {n : ℕ} (w : AffinePermutation n) (p : ℤ) (rho : Fin n → ℤ) :
    ∑ i, w.dotZero p rho i = 0 := by
  simp only [dotZero, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Equiv.sum_comp, w.balanced, mul_zero, zero_add, sub_self]

theorem inverse_dotZero {n : ℕ} (w : AffinePermutation n) (p : ℤ)
    (rho : Fin n → ℤ) (i : Fin n) :
    w.inverse.dotZero p rho i = -p * w.winding i + rho (w.residue i) - rho i := by
  simp [inverse, dotZero, neg_mul, mul_neg]

/-- An affine inversion-count expression. No Coxeter-length theorem is assumed. -/
def inversionCount {n : ℕ} (w : AffinePermutation n) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then ((w.entry j - w.entry i) / (n : ℤ)).natAbs else 0

end AffinePermutation

/-- A finite certificate supplies a residue permutation and its proposed inverse.
All conditions are checked, rather than trusted from the generator. -/
structure WindowCertificate (n : ℕ) where
  residue : Fin n → Fin n
  inverse : Fin n → Fin n
  winding : Fin n → ℤ

namespace WindowCertificate
def Valid {n : ℕ} (c : WindowCertificate n) : Prop :=
  (∀ i, c.inverse (c.residue i) = i) ∧
  (∀ i, c.residue (c.inverse i) = i) ∧ ∑ i, c.winding i = 0

instance {n : ℕ} (c : WindowCertificate n) : Decidable c.Valid := inferInstanceAs
  (Decidable ((∀ i, c.inverse (c.residue i) = i) ∧
    (∀ i, c.residue (c.inverse i) = i) ∧ ∑ i, c.winding i = 0))

def check {n : ℕ} (c : WindowCertificate n) : Bool := decide c.Valid

theorem check_sound {n : ℕ} (c : WindowCertificate n) (h : c.check = true) : c.Valid :=
  of_decide_eq_true h

theorem check_complete {n : ℕ} (c : WindowCertificate n) (h : c.Valid) : c.check = true :=
  decide_eq_true h

def toAffine {n : ℕ} (c : WindowCertificate n) (h : c.check = true) : AffinePermutation n where
  residue := ⟨c.residue, c.inverse, (check_sound c h).1, (check_sound c h).2.1⟩
  winding := c.winding
  balanced := (check_sound c h).2.2
end WindowCertificate

/-- The manuscript's input formula, defined independently of the certificates.
Here `i` is one-based. Inputs outside `2 ≤ m`, `1 ≤ j ≤ m` are not asserted valid. -/
def familyShift (m j i : ℕ) : ℤ :=
  if (1 ≤ i ∧ i < j) ∨ i = m + 2 then -1
  else if i = m ∨ (2*m+1-j+2 ≤ i ∧ i ≤ 2*m+1) then 1 else 0

def familyWindow (m j : ℕ) : List ℤ :=
  (((List.range (2*m+1)).map fun a =>
    let i : ℕ := a+1
    (i : ℤ) + (2*m+1 : ℕ) * familyShift m j i)).mergeSort (· ≤ ·)

/-- Row blocks `[1,m]`, `{m+1}`, `[m+2,2m+1]`. -/
def inRow (m : ℕ) (row : Fin 3) (x : ℤ) : Bool :=
  if row.val = 0 then decide (1 ≤ x ∧ x ≤ (m : ℤ))
  else if row.val = 1 then decide (x = (m : ℤ)+1)
  else decide ((m : ℤ)+2 ≤ x ∧ x ≤ 2*(m : ℤ)+1)

/-- Counts the image of the translated source block. `shift=-1,0,1`
correspond to periodic matrix columns `-2,1,4`, respectively. -/
def matrixEntry (m : ℕ) (w : AffinePermutation (2*m+1)) (row : Fin 3)
    (shift : ℤ) : ℕ :=
  (w.window.filter fun x => inRow m row (x + (2*m+1 : ℕ)*shift)).length

def matrixWindow (m : ℕ) (w : AffinePermutation (2*m+1)) : List (List ℕ) :=
  List.ofFn fun row : Fin 3 => [-1, 0, 1].map (matrixEntry m w row)

def prescribedMatrix (m j : ℕ) : List (List ℕ) :=
  [[1,m-j,j-1],[0,1,0],[j-1,m-j,1]]

/-- Coordinate tests for dominance/restrictedness and affine regularity.
They do not assert a highest-weight classification of representations. -/
def DominantRestricted {n : ℕ} (p : ℤ) (x : Fin n → ℤ) : Prop :=
  ∀ i j, i.val + 1 = j.val → 0 ≤ x i - x j ∧ x i - x j < p

def Regular {n : ℕ} (p : ℤ) (rho x : Fin n → ℤ) : Prop :=
  ∀ i j, i ≠ j → (x i + rho i - x j - rho j) % p ≠ 0

instance {n : ℕ} (p : ℤ) (x : Fin n → ℤ) : Decidable (DominantRestricted p x) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, i.val + 1 = j.val → 0 ≤ x i - x j ∧ x i - x j < p))

instance {n : ℕ} (p : ℤ) (rho x : Fin n → ℤ) : Decidable (Regular p rho x) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, i ≠ j → (x i + rho i - x j - rho j) % p ≠ 0))

end Guralnick
