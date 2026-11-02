import Guralnick.AffineLatticePosition
import Guralnick.FamilyMatrix
import Mathlib.Data.Int.Interval

/-!
# A precise generic periodic orbit-matrix input

Every object in this interface is fixed independently: integer intervals,
actual affine permutations, explicit Laurent coordinate modules, and actual
intersection/sum subquotients. The unformalized input is the standard
periodic-flag coordinate-dimension theorem underlying the BLM/Lusztig
orbit-matrix parametrization. It contains no special-family coefficient,
gallery formula, canonical correction or cohomology conclusion.

The subquotient convention is Cui, arXiv:1407.4557v3, §7.1, pp. 21–22;
the permutation block formula is the unnumbered Du--Fu bijection immediately
before (2.0.3), arXiv:1311.1868, §2, p. 5. The source inputs are now stated on independent polynomial Laurent
cut modules in `PolynomialOrbitCoordinates.Input`. The completed arbitrary
coordinate-change interface below is derived by
`PolynomialOrbitCoordinates.Input.toCompleted`, using actual quotient
linear equivalences. Finiteness is proved from lattice bounds. All four polynomial dimension
and order formulas are now proved from the actual Laurent monomial basis
in `PolynomialOrbitCounting`, which supplies the final input bundle.
-/

noncomputable section

namespace Guralnick.OrbitMatrix

open LaurentLattice AffineLatticePosition LatticeGallery
open Classical

variable (k : Type*) [Field k] (N : ℕ) [NeZero N]

/-- Highest included period at the degree-a cut. The coordinate vector
`(i,q)` has integer index i+1+N*q, so this cut has periodic index N+a:
the degree-zero lattice is k[[t]]^N. Shifting every row/source cut by N
does not change any displayed count, since an affine window commutes
with the period shift. -/
def cutLevel (a : ℤ) (i : Fin N) : ℤ := (a-(i.val+1))/N + 1

theorem cutLevel_nat (a : ℕ) (ha : a ≤ N) (i : Fin N) :
    cutLevel N a i = if i.val < a then 1 else 0 := by
  have hN : (0 : ℤ) < N := by exact_mod_cast (NeZero.pos N)
  have hi := i.isLt
  unfold cutLevel
  by_cases h : i.val < a
  · rw [if_pos h, Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    rfl
  · rw [if_neg h]
    have he : ((a : ℤ)-(i.val+1))/(N : ℤ) = -1 := by
      apply (Int.ediv_eq_iff_of_pos hN).mpr
      constructor <;> omega
    omega

/-- The ordinary periodic coordinate lattice at any integer cut. -/
def cutModule (a : ℤ) : Submodule (PowerSeries k) (Ambient k N) :=
  Submodule.span (PowerSeries k)
    (Set.range (fun i : Fin N => coordinateVector k N i (cutLevel N a i)))

theorem cutModule_nat (a : ℕ) (ha : a ≤ N) :
    cutModule k N a = coordinateModule k N a := by
  unfold cutModule coordinateModule
  simp_rw [cutLevel_nat N a ha]

/-- A target cut in a common Laurent basis. -/
def targetCut (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N) (a : ℤ) :
    Submodule k (Ambient k N) := (mapModule k N g (cutModule k N a)).restrictScalars k

/-- A source cut in that same basis, with its specified affine window. -/
def sourceCut (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a : ℤ) : Submodule k (Ambient k N) :=
  (mapModule k N ((windowEquiv k N w).trans g) (cutModule k N a)).restrictScalars k

/-- The literal finite block intersection |(a,b] ∩ w((c,d])|. -/
def blockCount (w : AffinePermutation N) (a b c d : ℤ) : ℕ :=
  ((Finset.Ioc a b).filter (fun x => c < w.onIntegers.symm x ∧ w.onIntegers.symm x ≤ d)).card

/-- The cumulative row count |{x∈(a,b] : w^-1(x)≤c}|. -/
def cumulativeCount (w : AffinePermutation N) (a b c : ℤ) : ℕ :=
  ((Finset.Ioc a b).filter (fun x => w.onIntegers.symm x ≤ c)).card

/-- Actual subquotient whose dimension is a periodic matrix entry. -/
abbrev BlockQuotient (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b c d : ℤ) :=
  QuotientSpace
    ((targetCut k N g a ⊓ sourceCut k N g w d) ⊔
      (targetCut k N g b ⊓ sourceCut k N g w c))
    (targetCut k N g b ⊓ sourceCut k N g w d)

/-- Actual cumulative intersection in the row interval, used for the
intersection dimensions of I₀,K₀ with the target quotient flag. -/
abbrev CumulativeQuotient (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b c : ℤ) :=
  QuotientSpace (targetCut k N g a)
    (targetCut k N g b ⊓ (sourceCut k N g w c ⊔ targetCut k N g a))

/-- Generic lattice-coordinate theorem. The finite-dimensionality clauses
prevent an infinite quotient's default `finrank=0` from certifying a count.
This compatibility interface is supplied by the proved polynomial
coordinate formulas and the proved completion/coordinate-change maps. -/
structure CoordinateDimensionInput : Prop where
  block_finite : ∀ (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b c d : ℤ), a ≤ b → c ≤ d →
      FiniteDimensional k (BlockQuotient k N g w a b c d)
  block_dimension : ∀ (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b c d : ℤ), a ≤ b → c ≤ d →
      Module.finrank k (BlockQuotient k N g w a b c d) = blockCount N w a b c d
  cumulative_finite : ∀ (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b c : ℤ), a ≤ b →
      FiniteDimensional k (CumulativeQuotient k N g w a b c)
  cumulative_dimension : ∀ (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b c : ℤ), a ≤ b →
      Module.finrank k (CumulativeQuotient k N g w a b c) = cumulativeCount N w a b c
  source_le_target : ∀ (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b : ℤ),
      sourceCut k N g w b ≤ targetCut k N g a ↔
        ∀ i : ℤ, i ≤ b → w.onIntegers i ≤ a
  target_le_source : ∀ (g : Ambient k N ≃ₗ[LaurentSeries k] Ambient k N)
    (w : AffinePermutation N) (a b : ℤ),
      targetCut k N g a ≤ sourceCut k N g w b ↔
        ∀ i : ℤ, i ≤ a → w.onIntegers.symm i ≤ b

/-- The block count is a difference of two cumulative counts, proved by
partitioning the actual finite interval. -/
theorem block_add_cumulative (w : AffinePermutation N) (a b c d : ℤ) (hcd : c ≤ d) :
    blockCount N w a b c d + cumulativeCount N w a b c = cumulativeCount N w a b d := by
  classical
  unfold blockCount cumulativeCount
  let s := (Finset.Ioc a b).filter (fun x => w.onIntegers.symm x ≤ d)
  have he : (s.filter (fun x => c < w.onIntegers.symm x)) =
      (Finset.Ioc a b).filter (fun x => c < w.onIntegers.symm x ∧ w.onIntegers.symm x ≤ d) := by
    ext x
    simp only [s, Finset.mem_filter]
    tauto
  have hf : (s.filter (fun x => ¬ c < w.onIntegers.symm x)) =
      (Finset.Ioc a b).filter (fun x => w.onIntegers.symm x ≤ c) := by
    ext x
    simp only [s, Finset.mem_filter, not_lt]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,h.2.trans hcd⟩,h.2⟩
  have hdis : Disjoint (s.filter (fun x => c < w.onIntegers.symm x))
      (s.filter (fun x => ¬ c < w.onIntegers.symm x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
  have hunion : (s.filter (fun x => c < w.onIntegers.symm x)) ∪
      (s.filter (fun x => ¬ c < w.onIntegers.symm x)) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have h := Finset.card_union_of_disjoint hdis
  rw [hunion,he,hf] at h
  exact h.symm

/-- Inversion of the actual affine permutation agrees with inversion of
its periodic integer bijection. -/
theorem onIntegers_inv (w : AffinePermutation N) :
    (w⁻¹).onIntegers = w.onIntegers.symm := by
  apply Equiv.ext
  intro x
  simp [AffinePermutation.onIntegers, AffinePermutation.equiv,
    AffinePermutation.inv_eq_inverse, AffinePermutation.inverse, sub_eq_add_neg]

/-- The ordinary residues enumerate one translated integer source packet. -/
def packetResidues (q : ℤ) : Fin N ≃ {x : ℤ // (N : ℤ)*q < x ∧ x ≤ (N : ℤ)*q+N} where
  toFun i := ⟨(i.val : ℤ)+1+N*q, by have hi := i.isLt; constructor <;> omega⟩
  invFun x := ⟨(x.val-N*q-1).toNat, by have hx := x.property; omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv x := by apply Subtype.ext; dsimp; have hx := x.property; omega

/-- The permutation of periodic integers evaluates a translated packet
using the actual affine window, with no change of convention. -/
theorem onIntegers_packet (w : AffinePermutation N) (i : Fin N) (q : ℤ) :
    w.onIntegers ((i.val : ℤ)+1+N*q) = w.entry i+N*q := by
  rw [← AffinePermutation.integerIndex_apply (i,q), AffinePermutation.onIntegers_index]
  rw [AffinePermutation.integerIndex_apply]
  change ((w.residue i).val : ℤ)+1+N*(q+w.winding i) = w.entry i+N*q
  unfold AffinePermutation.entry
  ring

theorem entry_injective (w : AffinePermutation N) : Function.Injective w.entry := by
  intro i j hij
  have hi := onIntegers_packet N w i 0
  have hj := onIntegers_packet N w j 0
  simp only [mul_zero, add_zero] at hi hj
  have h := w.onIntegers.injective (hi.trans (hij.trans hj.symm))
  apply Fin.ext
  omega

/-- The window image is exactly the image of its translated source interval. -/
theorem packet_image (w : AffinePermutation N) (q : ℤ) :
    (Finset.Ioc ((N : ℤ)*q) ((N : ℤ)*q+N)).image w.onIntegers =
      Finset.univ.image (fun i : Fin N => w.entry i+N*q) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Ioc, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z,hz,rfl⟩
    let i := (packetResidues N q).symm ⟨z,hz⟩
    have hi := congrArg Subtype.val ((packetResidues N q).apply_symm_apply ⟨z,hz⟩)
    refine ⟨i, ?_⟩
    change ((i.val : ℤ)+1+N*q) = z at hi
    rw [← onIntegers_packet N w i q, hi]
  · rintro ⟨i,rfl⟩
    refine ⟨(packetResidues N q i).val, (packetResidues N q i).property, ?_⟩
    exact onIntegers_packet N w i q

/-- The generic block entry is literally the checked affine-window count
when the source block is a single translated packet. -/
theorem blockCount_packet (w : AffinePermutation N) (a b q : ℤ) :
    blockCount N w a b ((N : ℤ)*q) ((N : ℤ)*q+N) =
      ((w.window.map (fun x => x+N*q)).filter (fun x => decide (a < x ∧ x ≤ b))).length := by
  have hset : (Finset.Ioc a b).filter (fun x =>
      (N : ℤ)*q < w.onIntegers.symm x ∧ w.onIntegers.symm x ≤ (N : ℤ)*q+N) =
      ((Finset.Ioc ((N : ℤ)*q) ((N : ℤ)*q+N)).image w.onIntegers).filter
        (fun x => a < x ∧ x ≤ b) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨hx,hsource⟩
      exact ⟨⟨w.onIntegers.symm x,hsource,w.onIntegers.apply_symm_apply x⟩,hx⟩
    · rintro ⟨⟨z,hz,hzx⟩,hx⟩
      subst x
      exact ⟨hx, by simpa only [Equiv.symm_apply_apply] using hz⟩
  unfold blockCount
  rw [hset, packet_image]
  have himage : Finset.univ.image (fun i : Fin N => w.entry i+N*q) =
      (w.window.map (fun x => x+N*q)).toFinset := by
    rw [AffinePermutation.window, List.map_ofFn]
    exact Fin.univ_image_def _
  rw [himage]
  have hfilter := List.toFinset_filter (w.window.map (fun x => x+N*q))
    (fun x => decide (a < x ∧ x ≤ b))
  simp only [decide_eq_true_eq] at hfilter
  rw [← hfilter]
  apply List.toFinset_card_of_nodup
  apply List.Nodup.filter
  rw [AffinePermutation.window, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro i j hij
  apply entry_injective N w
  change w.entry i+N*q = w.entry j+N*q at hij
  omega

/-- Boundaries of the paper's three output packets, in the same integer
coordinates as its independently defined `matrixEntry`. -/
def familyRowLower (m : ℕ) (row : Fin 3) : ℤ := ![0,(m : ℤ),m+1] row
def familyRowUpper (m : ℕ) (row : Fin 3) : ℤ := ![(m : ℤ),m+1,2*m+1] row

theorem inRow_interval (m : ℕ) (row : Fin 3) (x : ℤ) :
    inRow m row x = decide (familyRowLower m row < x ∧ x ≤ familyRowUpper m row) := by
  apply Bool.eq_iff_iff.mpr
  fin_cases row <;> simp [inRow, familyRowLower, familyRowUpper] <;> omega

/-- The new generic orbit-block count is identified with the pre-existing
window checker for every affine permutation, not just this family. -/
theorem blockCount_eq_matrixEntry (m : ℕ) (w : AffinePermutation (2*m+1))
    (row : Fin 3) (q : ℤ) :
    blockCount (2*m+1) w (familyRowLower m row) (familyRowUpper m row)
      ((2*m+1 : ℕ)*q) (((2*m+1 : ℕ) : ℤ)*q+(2*m+1 : ℕ)) =
        matrixEntry m w row q := by
  rw [blockCount_packet, matrixEntry, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro x _
  exact (inRow_interval m row (x+(2*m+1 : ℕ)*q)).symm

/-- Uniform bridge from the generic orbit-matrix count to the actual
manuscript family matrix, using the independently proved window formula. -/
theorem family_blockCount {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (row col : Fin 3) :
    blockCount (2*m+1) (Family.affine hm hj hjm)
      (familyRowLower m row) (familyRowUpper m row)
      (((2*m+1 : ℕ) : ℤ)*Family.columnShift col)
      (((2*m+1 : ℕ) : ℤ)*Family.columnShift col+(2*m+1 : ℕ)) =
      Family.prescribedArray m j row col := by
  rw [blockCount_eq_matrixEntry, Family.matrixEntry_eq_prescribedArray hm hj hjm]

/-- Multiplication on the right by a finite permutation only rearranges
the packet. Its winding and all full-packet block counts are preserved. -/
theorem matrixEntry_right_finite (m : ℕ) (w : AffinePermutation (2*m+1))
    (σ : Equiv.Perm (Fin (2*m+1))) (row : Fin 3) (q : ℤ) :
    matrixEntry m (w * AffinePermutation.finiteEmbedding (2*m+1) σ) row q =
      matrixEntry m w row q := by
  have hp : (w * AffinePermutation.finiteEmbedding (2*m+1) σ).window.Perm w.window := by
    unfold AffinePermutation.window
    have he : (w * AffinePermutation.finiteEmbedding (2*m+1) σ).entry =
        w.entry ∘ σ := by
      funext i
      simp [AffinePermutation.entry, AffinePermutation.finiteEmbedding,
        Equiv.Perm.mul_apply]
    rw [he]
    exact σ.ofFn_comp_perm _
  exact (hp.filter (fun x => inRow m row (x+(2*m+1 : ℕ)*q))).length_eq

/-- The actual ordinary KL upper endpoint C=u*w₀ has precisely the same
three-row matrix as u; the prescribed lower/source packet is unchanged. -/
theorem family_upper_blockCount {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (row col : Fin 3) :
    blockCount (2*m+1) (Family.upper hm hj hjm)
      (familyRowLower m row) (familyRowUpper m row)
      (((2*m+1 : ℕ) : ℤ)*Family.columnShift col)
      (((2*m+1 : ℕ) : ℤ)*Family.columnShift col+(2*m+1 : ℕ)) =
      Family.prescribedArray m j row col := by
  rw [blockCount_eq_matrixEntry, Family.upper, AffinePermutation.longest,
    matrixEntry_right_finite, Family.matrixEntry_eq_prescribedArray hm hj hjm]

/-- The displayed family matrix is the dimension matrix of the actual
coordinate-lattice pair, conditional only on the generic coordinate theorem. -/
theorem family_block_dimension {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (input : CoordinateDimensionInput k (2*m+1))
    (g : Ambient k (2*m+1) ≃ₗ[LaurentSeries k] Ambient k (2*m+1))
    (row col : Fin 3) :
    Module.finrank k (BlockQuotient k (2*m+1) g (Family.affine hm hj hjm)
      (familyRowLower m row) (familyRowUpper m row)
      (((2*m+1 : ℕ) : ℤ)*Family.columnShift col)
      (((2*m+1 : ℕ) : ℤ)*Family.columnShift col+(2*m+1 : ℕ))) =
      Family.prescribedArray m j row col := by
  rw [input.block_dimension _ _ _ _ _ _ ?_ ?_, family_blockCount hm hj hjm]
  · fin_cases row <;> simp [familyRowLower, familyRowUpper] <;> omega
  · omega

end Guralnick.OrbitMatrix
