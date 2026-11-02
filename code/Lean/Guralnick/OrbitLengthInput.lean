import Guralnick.OrbitMatrix
import Guralnick.FiniteBlocks
import Guralnick.WindowPacketMatrix

/-!
# General periodic matrix/length and orbit-classification inputs

The remaining external results are stated for every positive output
composition and every maximal ordinary double-coset index, with the fixed
full spherical source. The entries are literal output-residue counts of
the inverse affine window. No special matrix, family length, gallery,
canonical correction or coefficient is an input.

These are the three-column restrictions of the general periodic orbit
classification and dimension/length dictionary: Cui, arXiv:1407.4557v3,
§7.1 and Lemma 7.2, together with the block-intersection convention of
Du--Fu, arXiv:1311.1868, §2, the unnumbered block bijection before (2.0.3).
-/
noncomputable section
namespace Guralnick.OrbitMatrix
open Classical
open FiniteBlocks CanonicalSchur

/-- Actual three-column entries for an arbitrary positive row composition
whose first cut is zero. Each row is the interval between successive
partial sums of the packet sizes. -/
def compositionEntries {N : ℕ} (A : FiniteBlocks.Composition N) (w : AffinePermutation N)
    (row : Fin A.packets.length) (col : Fin 3) : ℕ :=
  (Finset.univ.filter fun i : Fin N =>
    (A.packets.take row.val).sum ≤ i.val ∧
      i.val < (A.packets.take (row.val+1)).sum ∧
        (w⁻¹).winding i = Family.columnShift col).card

/-- General cited dictionary, restricted to bounded three-column support.
The source is explicitly the finite spherical parabolic, and maximality
is expressed through actual Coxeter descents. Equal matrices identify
maximal representatives, not arbitrary elements of a double coset. -/
structure ThreeColumnLengthInput {N : ℕ} [NeZero N]
    (c : Hecke.WindowCoxeter N) : Prop where
  dimension_length : ∀ (A : FiniteBlocks.Composition N), A.cut.val = 0 →
    ∀ (w : AffinePermutation N), WindowPacketMatrix.Supported w →
      DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) w →
      PeriodicMatrix.dimension (fun i j => (compositionEntries A w i j : ℤ)) =
        (c.system.length w : ℤ) - c.system.length (AffinePermutation.longest N)
  /-- Converse of the general maximal-length formula. The source condition
  is explicit, and the row composition and window remain arbitrary. This
  is the usual uniqueness of the longest element in a finite-parabolic
  double coset, together with its periodic dimension formula. -/
  maximal_of_dimension : ∀ (A : FiniteBlocks.Composition N), A.cut.val = 0 →
    ∀ (w : AffinePermutation N), WindowPacketMatrix.Supported w →
      (∀ i ∈ (CanonicalChains.source (NeZero.pos N)).val,
        c.system.IsRightDescent w i) →
      (c.system.length w : ℤ) - c.system.length (AffinePermutation.longest N) =
        PeriodicMatrix.dimension (fun i j => (compositionEntries A w i j : ℤ)) →
      DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) w
  matrix_injective : ∀ (A : FiniteBlocks.Composition N), A.cut.val = 0 →
    ∀ (u v : AffinePermutation N), WindowPacketMatrix.Supported u →
      WindowPacketMatrix.Supported v →
      DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) u →
      DoubleMaximal c A.index (CanonicalChains.source (NeZero.pos N)) v →
      compositionEntries A u = compositionEntries A v → u = v

/-- The general row-interval definition specializes to the independently
constructed actual three-row packet matrix. -/
theorem compositionEntries_output {m : ℕ} (hm : 2 ≤ m)
    (w : AffinePermutation (2*m+1)) (row col : Fin 3) :
    compositionEntries (FiniteBlocks.Family.output hm) w row col =
      WindowPacketMatrix.entries m w row col := by
  unfold compositionEntries WindowPacketMatrix.entries
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  fin_cases row <;>
    simp [FiniteBlocks.Family.output,WindowPacketMatrix.rowOf_zero,
      WindowPacketMatrix.rowOf_one,WindowPacketMatrix.rowOf_two] <;>
    have hi := i.isLt <;> omega

/-- The full spherical boundary has one literal row. -/
theorem compositionEntries_source {m : ℕ} (hm : 2 ≤ m)
    (w : AffinePermutation (2*m+1)) (row : Fin 1) (col : Fin 3) :
    compositionEntries (FiniteBlocks.Family.source hm) w row col =
      (Finset.univ.filter fun i : Fin (2*m+1) =>
        (w⁻¹).winding i = Family.columnShift col).card := by
  fin_cases row
  unfold compositionEntries
  congr 1
  ext i
  simp [FiniteBlocks.Family.source,i.isLt]

end Guralnick.OrbitMatrix
