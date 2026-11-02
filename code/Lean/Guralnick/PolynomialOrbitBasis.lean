import Guralnick.PolynomialOrbitCoordinates
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The literal Laurent monomial basis and periodic cuts

The integer indexing is chosen so that the ordinary polynomial lattice
has cut zero. The monomial at integer z has index at most a precisely
when it belongs to the polynomial cut at a; affine windows permute these
actual monomials by their actual action on the integers.
-/
noncomputable section
namespace Guralnick.PolynomialOrbitCounting
open PolynomialLattice PolynomialAffineCoordinates PolynomialOrbitCoordinates
open scoped BigOperators
variable (k : Type) [Field k] (N : ℕ) [NeZero N]

/-- The Laurent exponent corresponding to period q is -q-1. -/
def exponentPeriod : ℤ ≃ ℤ where
  toFun q := -q-1
  invFun q := -q-1
  left_inv q := by dsimp; omega
  right_inv q := by dsimp; omega

/-- The ordinary coordinate monomial basis, indexed by coordinate and exponent. -/
def monomialBasis : Basis (Fin N × ℤ) k (PolynomialLattice.Ambient k N) :=
  ((Finsupp.basis fun _ : Fin N => (Finsupp.basisSingleOne : Basis ℤ k (ℤ →₀ k))).map
    (Finsupp.linearEquivFunOnFinite k (ℤ →₀ k) (Fin N))).reindex
      (Equiv.sigmaEquivProd (Fin N) ℤ)

theorem monomialBasis_apply (i : Fin N) (r : ℤ) :
    monomialBasis k N (i,r) = Pi.single i (LaurentPolynomial.T r) := by
  let b := (Finsupp.basis fun _ : Fin N =>
    (Finsupp.basisSingleOne : Basis ℤ k (ℤ →₀ k))).map
      (Finsupp.linearEquivFunOnFinite k (ℤ →₀ k) (Fin N))
  have h₁ := b.reindex_apply (Equiv.sigmaEquivProd (Fin N) ℤ) (i,r)
  apply h₁.trans
  change b ⟨i,r⟩ = _
  rw [show b ⟨i,r⟩ = (Finsupp.linearEquivFunOnFinite k (ℤ →₀ k) (Fin N))
      ((Finsupp.basis fun _ : Fin N => (Finsupp.basisSingleOne : Basis ℤ k (ℤ →₀ k)))
        ⟨i,r⟩) from Basis.map_apply _ _ _]
  rw [Finsupp.coe_basis,Finsupp.coe_basisSingleOne,Finsupp.linearEquivFunOnFinite_single]
  rfl

/-- The actual Laurent monomial basis in affine integer order. -/
def integerBasis : Basis ℤ k (PolynomialLattice.Ambient k N) :=
  (monomialBasis k N).reindex
    ((Equiv.prodCongr (Equiv.refl (Fin N)) exponentPeriod).trans (AffinePermutation.integerIndex N))

theorem integerBasis_index (i : Fin N) (q : ℤ) :
    integerBasis k N (AffinePermutation.integerIndex N (i,q)) =
      coordinateVector k N i (q+1) := by
  simp only [integerBasis,Basis.reindex_apply,Equiv.symm_trans_apply,
    Equiv.symm_apply_apply,Equiv.prodCongr_symm,Equiv.prodCongr_apply,Equiv.refl_symm,
    Equiv.refl_apply]
  rw [monomialBasis_apply]
  change (Pi.single i (LaurentPolynomial.T (-q-1)) : PolynomialLattice.Ambient k N) =
    (Pi.single i (LaurentPolynomial.T (-(q+1))) : PolynomialLattice.Ambient k N)
  rw [show -q-1 = -(q+1) by omega]

/-- The polynomial parameter lowers the periodic integer label. -/
theorem X_pow_coordinateVector (d : ℕ) (i : Fin N) (q : ℤ) :
    (Polynomial.X : Polynomial k)^d • coordinateVector k N i q =
      coordinateVector k N i (q-d) := by
  classical
  funext j
  by_cases h : i = j
  · subst j
    simp only [coordinateVector,Pi.smul_apply,Pi.single_eq_same]
    change Polynomial.toLaurent (Polynomial.X^d) * LaurentPolynomial.T (-q) =
      LaurentPolynomial.T (-(q-d))
    rw [Polynomial.toLaurent_X_pow,← LaurentPolynomial.T_add]
    congr 1
    omega
  · simp [coordinateVector,h]

/-- Every affine window permutes the literal monomial basis as its integer action. -/
theorem window_coordinateVector (w : AffinePermutation N) (i : Fin N) (q : ℤ) :
    windowEquiv k N w (coordinateVector k N i q) =
      coordinateVector k N (w.residue i) (q+w.winding i) := by
  classical
  funext j
  by_cases h : w.residue i = j
  · subst j
    simp [windowEquiv,coordinateVector,monomial,← LaurentPolynomial.T_add]
    rw [show (Equiv.symm w.residue) (w.residue i) = i from w.residue.symm_apply_apply i]
    rw [Pi.single_eq_same,← LaurentPolynomial.T_add]
    rw [add_comm (-q) (-w.winding i)]
  · have hi : i ≠ w.residue.symm j := by
      intro he
      exact h (by simpa using congrArg w.residue he)
    simp [windowEquiv,coordinateVector,h,hi]

theorem window_integerBasis (w : AffinePermutation N) (z : ℤ) :
    windowEquiv k N w (integerBasis k N z) = integerBasis k N (w.onIntegers z) := by
  obtain ⟨⟨i,q⟩,rfl⟩ := (AffinePermutation.integerIndex N).surjective z
  rw [integerBasis_index,AffinePermutation.onIntegers_index]
  change _ = integerBasis k N (AffinePermutation.integerIndex N (w.residue i,q+w.winding i))
  rw [integerBasis_index,window_coordinateVector]
  congr 1
  ring

/-- The cut level is exactly the affine integer inequality. -/
theorem index_le_cut_iff (a : ℤ) (i : Fin N) (q : ℤ) :
    AffinePermutation.integerIndex N (i,q) ≤ a ↔ q+1 ≤ OrbitMatrix.cutLevel N a i := by
  rw [AffinePermutation.integerIndex_apply]
  dsimp only [Prod.fst,Prod.snd]
  unfold OrbitMatrix.cutLevel
  have hN : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  have he : q ≤ (a-(i.val+1))/(N : ℤ) ↔ q*(N : ℤ) ≤ a-(i.val+1) :=
    Int.le_ediv_iff_mul_le hN
  rw [mul_comm q (N : ℤ)] at he
  omega

#print axioms integerBasis
#print axioms window_integerBasis
end Guralnick.PolynomialOrbitCounting
