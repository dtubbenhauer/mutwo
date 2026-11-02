import Guralnick.PolynomialOrbitBasis

/-! # Actual polynomial cuts as spans of the integer monomial basis -/
noncomputable section
namespace Guralnick.PolynomialOrbitCounting
open PolynomialLattice PolynomialAffineCoordinates PolynomialOrbitCoordinates
variable (k : Type) [Field k] (N : ℕ) [NeZero N]

/-- Integer basis support below a specified affine cut. -/
def cutSpan (a : ℤ) : Submodule k (PolynomialLattice.Ambient k N) :=
  Submodule.span k (integerBasis k N '' {z : ℤ | z ≤ a})

theorem basis_mem_cut (a z : ℤ) (hz : z ≤ a) : integerBasis k N z ∈ targetCut k N a := by
  obtain ⟨⟨i,q⟩,rfl⟩ := (AffinePermutation.integerIndex N).surjective z
  have hq := (index_le_cut_iff N a i q).mp hz
  let d := (OrbitMatrix.cutLevel N a i-(q+1)).toNat
  have hd : (d : ℤ) = OrbitMatrix.cutLevel N a i-(q+1) := Int.toNat_of_nonneg (by omega)
  have he := X_pow_coordinateVector k N d i (OrbitMatrix.cutLevel N a i)
  have hh : OrbitMatrix.cutLevel N a i-(d : ℤ) = q+1 := by omega
  rw [hh] at he
  rw [integerBasis_index,← he]
  exact (cutModule k N a).smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)

/-- Polynomial t-powers shift the affine label by a full period each. -/
theorem X_pow_integerBasis (d : ℕ) (z : ℤ) :
    (Polynomial.X : Polynomial k)^d • integerBasis k N z =
      integerBasis k N (z-(N : ℤ)*d) := by
  obtain ⟨⟨i,q⟩,rfl⟩ := (AffinePermutation.integerIndex N).surjective z
  have he : AffinePermutation.integerIndex N (i,q)-(N : ℤ)*d =
      AffinePermutation.integerIndex N (i,q-d) := by
    simp only [AffinePermutation.integerIndex_apply]
    ring
  rw [he,integerBasis_index,integerBasis_index,X_pow_coordinateVector]
  congr 1
  ring

theorem polynomial_C_smul (r : k) (x : PolynomialLattice.Ambient k N) :
    Polynomial.C r • x = r • x := by
  change (algebraMap k (Polynomial k) r) • x = r • x
  exact algebraMap_smul (Polynomial k) r x

/-- Polynomial multiplication preserves the span below a cut. -/
theorem polynomial_smul_basis (a : ℤ) (p : Polynomial k) (z : ℤ) (hz : z ≤ a) :
    p • integerBasis k N z ∈ cutSpan k N a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul]
    exact (cutSpan k N a).add_mem hp hq
  | monomial d r =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial,mul_smul,polynomial_C_smul,X_pow_integerBasis]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨z-(N : ℤ)*d,?_,rfl⟩
    change z-(N : ℤ)*d ≤ a
    have hprod : (0 : ℤ) ≤ (N : ℤ)*d := mul_nonneg (Int.natCast_nonneg N) (Int.natCast_nonneg d)
    omega

theorem polynomial_smul_cutSpan (a : ℤ) (p : Polynomial k)
    (x : PolynomialLattice.Ambient k N) (hx : x ∈ cutSpan k N a) :
    p • x ∈ cutSpan k N a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z,hz,rfl⟩ := hx
    exact polynomial_smul_basis k N a p z hz
  | zero => simpa using (cutSpan k N a).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [smul_add] using (cutSpan k N a).add_mem ihx ihy
  | smul r x hx ih =>
    rw [smul_comm]
    exact (cutSpan k N a).smul_mem r ih

/-- The polynomial module definition equals the actual monomial-support cut. -/
theorem targetCut_span (a : ℤ) : targetCut k N a = cutSpan k N a := by
  apply le_antisymm
  · intro x hx
    change x ∈ Submodule.span (Polynomial k) _ at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      let q := OrbitMatrix.cutLevel N a i-1
      have hq : AffinePermutation.integerIndex N (i,q) ≤ a :=
        (index_le_cut_iff N a i q).mpr (by dsimp [q]; omega)
      have hb : integerBasis k N (AffinePermutation.integerIndex N (i,q)) ∈ cutSpan k N a :=
        Submodule.subset_span ⟨_,hq,rfl⟩
      simpa only [integerBasis_index,q,sub_add_cancel] using hb
    | zero => exact (cutSpan k N a).zero_mem
    | add x y hx hy ihx ihy => exact (cutSpan k N a).add_mem ihx ihy
    | smul p x hx ih => exact polynomial_smul_cutSpan k N a p x ih
  · apply Submodule.span_le.mpr
    rintro x ⟨z,hz,rfl⟩
    exact basis_mem_cut k N a z hz

/-- The source is the span of precisely the integer monomials whose inverse
window labels lie below the source cut. -/
theorem sourceCut_span (w : AffinePermutation N) (a : ℤ) :
    sourceCut k N w a = Submodule.span k
      (integerBasis k N '' {z : ℤ | w.onIntegers.symm z ≤ a}) := by
  have he : sourceCut k N w a =
      (targetCut k N a).map ((windowEquiv k N w).restrictScalars k).toLinearMap := rfl
  rw [he,targetCut_span,cutSpan,Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨w.onIntegers z,?_,?_⟩
    · simpa using hz
    · exact (window_integerBasis k N w z).symm
  · rintro ⟨z,hz,rfl⟩
    refine ⟨integerBasis k N (w.onIntegers.symm z),⟨_,hz,rfl⟩,?_⟩
    change windowEquiv k N w (integerBasis k N (w.onIntegers.symm z)) = _
    rw [window_integerBasis,Equiv.apply_symm_apply]

#print axioms targetCut_span
#print axioms sourceCut_span
end Guralnick.PolynomialOrbitCounting
