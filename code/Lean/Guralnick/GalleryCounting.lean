import Guralnick.GalleryFlags
import Guralnick.CanonicalGallery
import Guralnick.CanonicalAuxiliary
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Counting the actual finite gallery configurations

The generic interface below concerns actual subspaces and their dimensions.
All of its fields are now proved in `FiniteFlagEnumeration`, by counting
independent frames and passing through actual quotient and flag
equivalences. The interface is retained to keep this module independent of
its enumeration proof; it is no longer an external assumption of the
final theorem. The four-case gallery count is derived from those counts.

Vinroot, *An Enumeration of Flags in Finite Vector Spaces*, §2, provides
background for the same Gaussian formulas, but supplies no assumed field
in the final proof. The line formula here uses mathlib's projective-space
cardinality theorem.
-/

noncomputable section

namespace Guralnick.GalleryCounting

open scoped BigOperators
open Polynomial GalleryFlags CanonicalGallery
open Classical
open scoped LinearAlgebra.Projectivization

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A two-step flag in an arbitrary subspace interval. -/
structure AdjacentFlag (lo up : Submodule k V) (m : ℕ) where
  I : Submodule k V
  K : Submodule k V
  lower_le : lo ≤ I
  middle_le : I ≤ K
  upper_le : K ≤ up
  I_dim : Module.finrank k I = m
  K_dim : Module.finrank k K = m+1

/-- An actual subspace in an interval, with its ambient dimension. -/
def IntermediateSubspace (lo up : Submodule k V) (j : ℕ) :=
  {U : Submodule k V // lo ≤ U ∧ U ≤ up ∧ Module.finrank k U = j}

/-- The residual gallery flag is exactly an ordinary interval flag. -/
def intervalFlagEquiv (I₀ K₀ L H : Submodule k V) (m : ℕ) :
    IntervalFlag I₀ K₀ L H m ≃ AdjacentFlag (I₀ ⊔ L) (K₀ ⊓ H) m where
  toFun f := ⟨f.I, f.K, f.lower_le, f.middle_le, f.upper_le, f.I_dim, f.K_dim⟩
  invFun f := ⟨f.I, f.K, f.lower_le, f.middle_le, f.upper_le, f.I_dim, f.K_dim⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- Generic finite-vector-space enumeration. These are the usual Gaussian
flag formulas, separate from every manuscript-specific gallery statement.
The positivity hypothesis on ambient dimension is necessary for the
hyperplane convention `dim V - 1` in natural numbers. -/
structure FiniteFlagCounts (k V : Type*) [Field k] [Finite k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Finite V] : Prop where
  hyperplanes (S : Submodule k V) (hV : 0 < Module.finrank k V) :
    (Nat.card {H : Submodule k V //
      Module.finrank k H = Module.finrank k V - 1 ∧ S ≤ H} : ℤ) =
      eval (Nat.card k : ℤ) (qInt ((Module.finrank k V : ℤ) - Module.finrank k S))
  subspaces (lo up : Submodule k V) (j : ℕ) (h : lo ≤ up) :
    (Nat.card (IntermediateSubspace lo up j) : ℤ) = eval (Nat.card k : ℤ)
      (qGauss ((Module.finrank k up : ℤ) - Module.finrank k lo)
        ((j : ℤ) - Module.finrank k lo))
  adjacent (lo up : Submodule k V) (m : ℕ) (h : lo ≤ up) :
    (Nat.card (AdjacentFlag lo up m) : ℤ) = eval (Nat.card k : ℤ)
      (qGauss ((Module.finrank k up : ℤ) - Module.finrank k lo)
        ((m : ℤ) - Module.finrank k lo) * qInt ((Module.finrank k up : ℤ) - m))

instance finiteSubmodule [Finite V] : Finite (Submodule k V) :=
  Finite.of_injective (fun S : Submodule k V => (S : Set V)) SetLike.coe_injective

instance finiteIntermediateSubspace [Finite V] (lo up : Submodule k V) (j : ℕ) :
    Finite (IntermediateSubspace lo up j) := by
  unfold IntermediateSubspace
  infer_instance

/-- A line of the ambient space lying in `S` is a line of the vector space `S`. -/
def linesInEquiv (S : Submodule k V) :
    {L : Submodule k V // Module.finrank k L = 1 ∧ L ≤ S} ≃
      {L : Submodule k S // Module.finrank k L = 1} where
  toFun L := ⟨L.val.comap S.subtype, by
    rw [(Submodule.comapSubtypeEquivOfLe L.property.2).finrank_eq]
    exact L.property.1⟩
  invFun L := ⟨L.val.map S.subtype, by simpa using L.property,
    Submodule.map_subtype_le S L.val⟩
  left_inv L := by
    apply Subtype.ext
    change (L.val.comap S.subtype).map S.subtype = L.val
    simp [Submodule.map_comap_subtype, inf_of_le_right L.property.2]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective L.val

/-- The standard line formula is already a consequence of mathlib. -/
theorem line_cardinality [Finite k] (S : Submodule k V) :
    (Nat.card {L : Submodule k V // Module.finrank k L = 1 ∧ L ≤ S} : ℤ) =
      eval (Nat.card k : ℤ) (qInt (Module.finrank k S)) := by
  rw [Nat.card_congr (linesInEquiv S)]
  rw [← Nat.card_congr (Projectivization.equivSubmodule k S)]
  rw [Projectivization.card_of_finrank k S rfl]
  simp [qInt, Gaussian.qInteger, Polynomial.eval_finset_sum]

/-- Lines in the first case are precisely the lines in `I₀ ∩ F`. -/
def lineZeroEquiv (I₀ K₀ F : Submodule k V) (h₀ : I₀ ≤ K₀) :
    {L : LineChoice K₀ F // L.val ≤ I₀} ≃
      {L : Submodule k V // Module.finrank k L = 1 ∧ L ≤ I₀ ⊓ F} where
  toFun L := ⟨L.val.val, L.val.property.1,
    le_inf L.property (L.val.property.2.trans inf_le_left)⟩
  invFun L := ⟨⟨L.val, L.property.1,
    le_inf (L.property.2.trans inf_le_right)
      ((L.property.2.trans inf_le_left).trans h₀)⟩,
    L.property.2.trans inf_le_left⟩
  left_inv L := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv L := by apply Subtype.ext; rfl

/-- Hyperplanes in the first case contain exactly the larger sum `F' + K₀`. -/
def hyperplaneZeroEquiv (I₀ K₀ F' : Submodule k V) (N : ℕ) (h₀ : I₀ ≤ K₀) :
    {H : HyperplaneChoice I₀ F' N // K₀ ≤ H.val} ≃
      {H : Submodule k V // Module.finrank k H = N-1 ∧ F' ⊔ K₀ ≤ H} where
  toFun H := ⟨H.val.val, H.val.property.1,
    sup_le (le_sup_left.trans H.val.property.2) H.property⟩
  invFun H := ⟨⟨H.val, H.property.1,
    sup_le (le_sup_left.trans H.property.2)
      (h₀.trans (le_sup_right.trans H.property.2))⟩,
    le_sup_right.trans H.property.2⟩
  left_inv H := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv H := by apply Subtype.ext; rfl

/-- A finite binary case split, expressed over the integers so subtraction
really counts the complementary case. -/
theorem sum_binary {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (x y : ℤ) :
    (∑ a : α, if p a then x else y) =
      (Nat.card {a : α // p a} : ℤ) * x +
      ((Nat.card α : ℤ) - Nat.card {a : α // p a}) * y := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [Nat.cast_sub (Fintype.card_subtype_le p)]

variable [Finite k] [Finite V] [FiniteDimensional k V]

omit [Finite V] [FiniteDimensional k V] in
theorem line_counts
    (I₀ K₀ F : Submodule k V) (h₀ : I₀ ≤ K₀) :
    (Nat.card (LineChoice K₀ F) : ℤ) =
        eval (Nat.card k : ℤ) (qInt (Module.finrank k (F ⊓ K₀ : Submodule k V))) ∧
    (Nat.card {L : LineChoice K₀ F // L.val ≤ I₀} : ℤ) =
        eval (Nat.card k : ℤ) (qInt (Module.finrank k (I₀ ⊓ F : Submodule k V))) := by
  constructor
  · exact line_cardinality (F ⊓ K₀)
  · rw [Nat.card_congr (lineZeroEquiv I₀ K₀ F h₀)]
    exact line_cardinality (I₀ ⊓ F)

theorem hyperplane_counts (hcount : FiniteFlagCounts k V)
    (I₀ K₀ F' : Submodule k V) (h₀ : I₀ ≤ K₀) (N : ℕ)
    (hN : 0 < N) (hV : Module.finrank k V = N) :
    (Nat.card (HyperplaneChoice I₀ F' N) : ℤ) =
        eval (Nat.card k : ℤ)
          (qInt ((N : ℤ) - Module.finrank k (F' ⊔ I₀ : Submodule k V))) ∧
    (Nat.card {H : HyperplaneChoice I₀ F' N // K₀ ≤ H.val} : ℤ) =
        eval (Nat.card k : ℤ)
          (qInt ((N : ℤ) - Module.finrank k (F' ⊔ K₀ : Submodule k V))) := by
  constructor
  · simpa only [hV, HyperplaneChoice] using hcount.hyperplanes (F' ⊔ I₀) (by omega)
  · rw [Nat.card_congr (hyperplaneZeroEquiv I₀ K₀ F' N h₀)]
    simpa only [hV] using hcount.hyperplanes (F' ⊔ K₀) (by omega)

omit [Finite k] [Finite V] [FiniteDimensional k V] in
theorem lineCase_le_one (I₀ L : Submodule k V) : lineCase I₀ L ≤ 1 := by
  unfold lineCase
  split_ifs <;> omega

omit [Finite k] [Finite V] [FiniteDimensional k V] in
theorem hyperplaneCase_le_one (K₀ H : Submodule k V) : hyperplaneCase K₀ H ≤ 1 := by
  unfold hyperplaneCase
  split_ifs <;> omega

/-- Independent binary choices give four products of actual cardinalities. -/
theorem sum_double_binary {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (x00 x01 x10 x11 : ℤ) :
    (∑ a : α, ∑ b : β,
      if p a then (if q b then x00 else x01) else (if q b then x10 else x11)) =
      (Nat.card {a : α // p a} : ℤ) * (Nat.card {b : β // q b} : ℤ) * x00 +
      (Nat.card {a : α // p a} : ℤ) *
        ((Nat.card β : ℤ) - Nat.card {b : β // q b}) * x01 +
      ((Nat.card α : ℤ) - Nat.card {a : α // p a}) *
        (Nat.card {b : β // q b} : ℤ) * x10 +
      ((Nat.card α : ℤ) - Nat.card {a : α // p a}) *
        ((Nat.card β : ℤ) - Nat.card {b : β // q b}) * x11 := by
  have h : (∑ a : α, ∑ b : β,
      if p a then (if q b then x00 else x01) else (if q b then x10 else x11)) =
      ∑ a : α, if p a then
        ((Nat.card {b : β // q b} : ℤ) * x00 +
          ((Nat.card β : ℤ) - Nat.card {b : β // q b}) * x01) else
        ((Nat.card {b : β // q b} : ℤ) * x10 +
          ((Nat.card β : ℤ) - Nat.card {b : β // q b}) * x11) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : p a <;> simp only [ha, if_true, if_false] <;> apply sum_binary
  rw [h, sum_binary]
  ring

/-- Substituting the proved interval dimensions in the generic flag formula.
The two case indicators are actual containment tests. -/
theorem interval_count (hcount : FiniteFlagCounts k V)
    {I₀ K₀ F F' : Submodule k V} {m r l : ℕ}
    (h₀ : I₀ ≤ K₀) (hF : F ≤ F') (hml : r+l=m)
    (hV : Module.finrank k V = 2*m+1)
    (hI₀ : Module.finrank k I₀ = r) (hK₀ : Module.finrank k K₀ = 2*m+1-r)
    (L : LineChoice K₀ F) (H : HyperplaneChoice I₀ F' (2*m+1)) :
    (Nat.card (IntervalFlag I₀ K₀ L.val H.val m) : ℤ) =
      eval (Nat.card k : ℤ)
        (qGauss (2*(l : ℤ)+1-lineCase I₀ L.val-hyperplaneCase K₀ H.val)
          ((l : ℤ)-lineCase I₀ L.val) * qInt ((l : ℤ)+1-hyperplaneCase K₀ H.val)) := by
  rw [Nat.card_congr (intervalFlagEquiv I₀ K₀ L.val H.val m)]
  rw [hcount.adjacent _ _ _ (choices_give_interval h₀ hF L H)]
  have hlo := lower_dimension I₀ L.val L.property.1
  have hup := upper_dimension K₀ H.val (2*m+1) (by omega) hV H.property.1
  have heps := lineCase_le_one I₀ L.val
  have heta := hyperplaneCase_le_one K₀ H.val
  have hlo' : (Module.finrank k (I₀ ⊔ L.val : Submodule k V) : ℤ) =
      r + lineCase I₀ L.val := by omega
  have hup' : (Module.finrank k (K₀ ⊓ H.val : Submodule k V) : ℤ) =
      2*(m : ℤ)+1-r-hyperplaneCase K₀ H.val := by omega
  rw [hlo', hup']
  congr 3 <;> omega

theorem interval_count_cases (hcount : FiniteFlagCounts k V)
    {I₀ K₀ F F' : Submodule k V} {m r l : ℕ}
    (h₀ : I₀ ≤ K₀) (hF : F ≤ F') (hml : r+l=m)
    (hV : Module.finrank k V = 2*m+1)
    (hI₀ : Module.finrank k I₀ = r) (hK₀ : Module.finrank k K₀ = 2*m+1-r)
    (L : LineChoice K₀ F) (H : HyperplaneChoice I₀ F' (2*m+1)) :
    (Nat.card (IntervalFlag I₀ K₀ L.val H.val m) : ℤ) =
      if L.val ≤ I₀ then
        (if K₀ ≤ H.val then
          eval (Nat.card k : ℤ) (qGauss (2*(l : ℤ)+1) l * qInt ((l : ℤ)+1)) else
          eval (Nat.card k : ℤ) (qGauss (2*(l : ℤ)) l * qInt l)) else
        (if K₀ ≤ H.val then
          eval (Nat.card k : ℤ) (qGauss (2*(l : ℤ)) ((l : ℤ)-1) * qInt ((l : ℤ)+1)) else
          eval (Nat.card k : ℤ) (qGauss (2*(l : ℤ)-1) ((l : ℤ)-1) * qInt l)) := by
  classical
  rw [interval_count hcount h₀ hF hml hV hI₀ hK₀ L H]
  by_cases hL : L.val ≤ I₀ <;> by_cases hH : K₀ ≤ H.val <;>
    simp [lineCase, hyperplaneCase, hL, hH]

/-- The manuscript's four-case polynomial, proved for its actual gallery
set from generic finite flag enumeration. The parameters are intersection
dimensions, not independent numerical encodings of an asserted answer. -/
theorem four_case_count (hcount : FiniteFlagCounts k V)
    {I₀ K₀ F F' : Submodule k V} {m r l : ℕ} {a s β δ : ℤ}
    (h₀ : I₀ ≤ K₀) (hF : F ≤ F') (hml : r+l=m)
    (hV : Module.finrank k V = 2*m+1)
    (hI₀ : Module.finrank k I₀ = r) (hK₀ : Module.finrank k K₀ = 2*m+1-r)
    (hF' : Module.finrank k F' = m+1)
    (ha : (Module.finrank k (I₀ ⊓ F : Submodule k V) : ℤ) = a)
    (hb : (Module.finrank k (I₀ ⊓ F' : Submodule k V) : ℤ) = a+β)
    (hc : (Module.finrank k (K₀ ⊓ F : Submodule k V) : ℤ) = l+s)
    (hd : (Module.finrank k (K₀ ⊓ F' : Submodule k V) : ℤ) = l+s+δ) :
    (Nat.card (Gallery I₀ K₀ F F' m (2*m+1)) : ℤ) =
      eval (Nat.card k : ℤ) (CanonicalGallery.count l a s β δ) := by
  classical
  letI : Fintype (LineChoice K₀ F) := Fintype.ofFinite _
  letI : Fintype (HyperplaneChoice I₀ F' (2*m+1)) := Fintype.ofFinite _
  have hsumI := Submodule.finrank_sup_add_finrank_inf_eq F' I₀
  have hsumK := Submodule.finrank_sup_add_finrank_inf_eq F' K₀
  rw [inf_comm F' I₀] at hsumI
  rw [inf_comm F' K₀] at hsumK
  have hcodimI : ((2*m+1 : ℕ) : ℤ) -
      Module.finrank k (F' ⊔ I₀ : Submodule k V) = l+a+β := by omega
  have hcodimK : ((2*m+1 : ℕ) : ℤ) -
      Module.finrank k (F' ⊔ K₀ : Submodule k V) = s+δ-1 := by omega
  obtain ⟨hL, hL₀⟩ := line_counts I₀ K₀ F h₀
  rw [inf_comm F K₀, hc] at hL
  rw [ha] at hL₀
  obtain ⟨hH, hH₀⟩ := hyperplane_counts hcount I₀ K₀ F' h₀ (2*m+1) (by omega) hV
  rw [hcodimI] at hH
  rw [hcodimK] at hH₀
  have hcard : (Nat.card (Gallery I₀ K₀ F F' m (2*m+1)) : ℤ) =
      ∑ L : LineChoice K₀ F, ∑ H : HyperplaneChoice I₀ F' (2*m+1),
        (Nat.card (IntervalFlag I₀ K₀ L.val H.val m) : ℤ) := by
    rw [gallery_cardinality]
    simp only [Nat.cast_sum]
  rw [hcard]
  simp_rw [interval_count_cases hcount h₀ hF hml hV hI₀ hK₀]
  rw [sum_double_binary, hL₀, hH₀, hL, hH]
  simp only [CanonicalGallery.count, term0, term1, term2, term3,
    eval_add, eval_mul, eval_sub]
  ring

/-- The source position gives exactly the raw Gaussian polynomial `Y` used
in the uniform cancellation theorem. -/
theorem count_source (m : ℕ) :
    CanonicalGallery.count m 0 0 0 1 = Gaussian.Y m := by
  cases m with
  | zero => simp [count_boundary, Gaussian.Y, Gaussian.qInteger]
  | succ n =>
    have hG : qGauss (2*((n+1 : ℕ) : ℤ)-1) (((n+1 : ℕ) : ℤ)-1) =
        Gaussian.qBinomial (2*(n+1)-1) ((n+1)-1) := by
      convert qGauss_nat (n := 2*(n+1)-1) (k := (n+1)-1) (by omega) using 1 <;>
        congr 1 <;> omega
    simp only [CanonicalGallery.count, term0, term1, term2, term3,
      add_zero, zero_add, sub_self, qInt_zero, mul_zero, zero_mul,
      sub_zero, qInt_nat, hG, Gaussian.Y]
    ring

/-- The full-rank boundary uses the same actual gallery formula. -/
theorem boundary_count (hcount : FiniteFlagCounts k V)
    {I₀ K₀ F F' : Submodule k V} {m : ℕ} {a s β δ : ℤ}
    (h₀ : I₀ ≤ K₀) (hF : F ≤ F')
    (hV : Module.finrank k V = 2*m+1)
    (hI₀ : Module.finrank k I₀ = m) (hK₀ : Module.finrank k K₀ = m+1)
    (hF' : Module.finrank k F' = m+1)
    (ha : (Module.finrank k (I₀ ⊓ F : Submodule k V) : ℤ) = a)
    (hb : (Module.finrank k (I₀ ⊓ F' : Submodule k V) : ℤ) = a+β)
    (hc : (Module.finrank k (K₀ ⊓ F : Submodule k V) : ℤ) = s)
    (hd : (Module.finrank k (K₀ ⊓ F' : Submodule k V) : ℤ) = s+δ) :
    (Nat.card (Gallery I₀ K₀ F F' m (2*m+1)) : ℤ) =
      eval (Nat.card k : ℤ) (qInt a * qInt (s+δ-1)) := by
  have h := four_case_count hcount h₀ hF (r := m) (l := 0) (by omega)
    hV hI₀ (by omega) hF' ha hb (by simpa using hc) (by simpa using hd)
  simpa only [Nat.cast_zero, count_boundary] using h

/-- At the source, the count is obtained from actual `⊥` and `⊤` endpoint
subspaces, and equals the polynomial subsequently used in cancellation. -/
theorem source_gallery_count (hcount : FiniteFlagCounts k V)
    {F F' : Submodule k V} {m : ℕ} (hF : F ≤ F')
    (hV : Module.finrank k V = 2*m+1)
    (hFd : Module.finrank k F = m) (hF'd : Module.finrank k F' = m+1) :
    (Nat.card (Gallery (⊥ : Submodule k V) ⊤ F F' m (2*m+1)) : ℤ) =
      eval (Nat.card k : ℤ) (Gaussian.Y m) := by
  rw [← count_source]
  apply four_case_count hcount bot_le hF (r := 0) (l := m) (a := 0)
    (s := 0) (β := 0) (δ := 1) (by omega) hV
  · simp
  · simp [hV]
  · exact hF'd
  · simp
  · simp
  · rw [top_inf_eq F, hFd]
    simp
  · rw [top_inf_eq F', hF'd]
    simp

/-- The exact configuration for a web retaining one line. -/
structure OneLineGallery (I₀ K₀ F : Submodule k V) (j : ℕ) where
  L : Submodule k V
  U : Submodule k V
  line_dim : Module.finrank k L = 1
  U_dim : Module.finrank k U = j
  line_le_F : L ≤ F
  line_le_U : L ≤ U
  I₀_le_U : I₀ ≤ U
  U_le_K₀ : U ≤ K₀

/-- Choosing the line first leaves a single subspace in an actual interval. -/
def oneLineGalleryEquiv (I₀ K₀ F : Submodule k V) (j : ℕ) :
    OneLineGallery I₀ K₀ F j ≃
      Σ L : LineChoice K₀ F, IntermediateSubspace (I₀ ⊔ L.val) K₀ j where
  toFun g := ⟨⟨g.L, g.line_dim, le_inf g.line_le_F (g.line_le_U.trans g.U_le_K₀)⟩,
    ⟨g.U, sup_le g.I₀_le_U g.line_le_U, g.U_le_K₀, g.U_dim⟩⟩
  invFun g := ⟨g.1.val, g.2.val, g.1.property.1, g.2.property.2.2,
    g.1.property.2.trans inf_le_left, le_sup_right.trans g.2.property.1,
    le_sup_left.trans g.2.property.1, g.2.property.2.1⟩
  left_inv g := by cases g; rfl
  right_inv g := by rcases g with ⟨⟨L,hL⟩,⟨U,hU⟩⟩; rfl

/-- The original two-case one-line formula, for actual configurations. -/
theorem one_line_count (hcount : FiniteFlagCounts k V)
    {I₀ K₀ F : Submodule k V} {j : ℕ} {n s d a b : ℤ}
    (h₀ : I₀ ≤ K₀)
    (hn : (Module.finrank k K₀ : ℤ) - Module.finrank k I₀ = n)
    (hs : (j : ℤ) - Module.finrank k I₀ = s)
    (ha : (Module.finrank k (I₀ ⊓ F : Submodule k V) : ℤ) = a)
    (hc : (Module.finrank k (K₀ ⊓ F : Submodule k V) : ℤ) = d+b) :
    (Nat.card (OneLineGallery I₀ K₀ F j) : ℤ) =
      eval (Nat.card k : ℤ) (CanonicalAuxiliary.oneLineCount n s d a b) := by
  classical
  letI : Fintype (LineChoice K₀ F) := Fintype.ofFinite _
  have hcase (L : LineChoice K₀ F) :
      (Nat.card (IntermediateSubspace (I₀ ⊔ L.val) K₀ j) : ℤ) =
        if L.val ≤ I₀ then eval (Nat.card k : ℤ) (qGauss n s) else
          eval (Nat.card k : ℤ) (qGauss (n-1) (s-1)) := by
    rw [hcount.subspaces _ _ _ (sup_le h₀ (L.property.2.trans inf_le_right))]
    have hlo := lower_dimension I₀ L.val L.property.1
    have hlo' : (Module.finrank k (I₀ ⊔ L.val : Submodule k V) : ℤ) =
        Module.finrank k I₀ + lineCase I₀ L.val := by omega
    rw [hlo']
    by_cases hL : L.val ≤ I₀ <;> simp only [lineCase, hL, if_true, if_false,
      Nat.cast_zero, Nat.cast_one, add_zero]
    · rw [hn, hs]
    · congr 2 <;> omega
  rw [Nat.card_congr (oneLineGalleryEquiv I₀ K₀ F j), Nat.card_sigma, Nat.cast_sum]
  simp_rw [hcase]
  rw [sum_binary]
  obtain ⟨hL, hL₀⟩ := line_counts I₀ K₀ F h₀
  rw [inf_comm F K₀, hc] at hL
  rw [ha] at hL₀
  rw [hL₀, hL]
  simp only [CanonicalAuxiliary.oneLineCount, eval_add, eval_mul, eval_sub]

/-- The source coefficient of the actual one-line configuration, including
the zero lower-index boundary when `j=0`. -/
theorem one_line_source_count (hcount : FiniteFlagCounts k V)
    {F : Submodule k V} {N j f : ℕ}
    (hV : Module.finrank k V = N) (hF : Module.finrank k F = f) :
    (Nat.card (OneLineGallery (⊥ : Submodule k V) ⊤ F j) : ℤ) =
      eval (Nat.card k : ℤ) (qInt f * qGauss ((N : ℤ)-1) ((j : ℤ)-1)) := by
  have h := one_line_count hcount (I₀ := ⊥) (K₀ := ⊤) (F := F) (j := j)
    (n := N) (s := j) (d := f) (a := 0) (b := 0) bot_le
    (by simp [hV]) (by simp) (by simp) (by rw [top_inf_eq F, hF]; simp)
  simpa only [CanonicalAuxiliary.oneLineCount, qInt_zero, zero_mul,
    zero_add, add_zero, sub_zero] using h

/-- The full-spherical finite configuration consists of one intermediate
subspace. Its interval-Grassmann count has no retained line or marking. -/
abbrev SphericalGallery (I₀ K₀ : Submodule k V) (s : ℕ) :=
  IntermediateSubspace I₀ K₀ s

theorem spherical_count (hcount : FiniteFlagCounts k V)
    {I₀ K₀ : Submodule k V} {N r s : ℕ} (h₀ : I₀ ≤ K₀)
    (hI₀ : Module.finrank k I₀ = r) (hK₀ : Module.finrank k K₀ = N-r) :
    (Nat.card (SphericalGallery I₀ K₀ s) : ℤ) =
      eval (Nat.card k : ℤ) (qGauss ((N : ℤ)-2*r) ((s : ℤ)-r)) := by
  have hle := Submodule.finrank_mono h₀
  have hr : r ≤ N := by omega
  rw [hcount.subspaces _ _ _ h₀, hI₀, hK₀, Nat.cast_sub hr]
  congr 2
  ring

theorem spherical_count_valid (hcount : FiniteFlagCounts k V)
    {I₀ K₀ : Submodule k V} {N r s : ℕ} (h₀ : I₀ ≤ K₀)
    (hI₀ : Module.finrank k I₀ = r) (hK₀ : Module.finrank k K₀ = N-r)
    (hrs : r ≤ s) (hsN : s ≤ N-r) :
    (Nat.card (SphericalGallery I₀ K₀ s) : ℤ) =
      eval (Nat.card k : ℤ) (Gaussian.qBinomial (N-2*r) (s-r)) := by
  rw [spherical_count hcount h₀ hI₀ hK₀]
  have hrN : 2*r ≤ N := by omega
  have hncast : ((N-2*r : ℕ) : ℤ) = (N : ℤ)-2*r := by omega
  rw [← hncast, ← Nat.cast_sub hrs]
  rw [qGauss_nat (by omega)]

/-- A rank beyond the requested intermediate dimension gives no galleries. -/
theorem spherical_count_zero (hcount : FiniteFlagCounts k V)
    {I₀ K₀ : Submodule k V} {N r s : ℕ} (h₀ : I₀ ≤ K₀)
    (hI₀ : Module.finrank k I₀ = r) (hK₀ : Module.finrank k K₀ = N-r)
    (hrs : s < r) : Nat.card (SphericalGallery I₀ K₀ s) = 0 := by
  have h := spherical_count hcount (s := s) h₀ hI₀ hK₀
  have hneg : ¬ (0 : ℤ) ≤ (s : ℤ)-r := by omega
  simp only [qGauss, hneg, false_and, if_false, eval_zero] at h
  exact_mod_cast h

end Guralnick.GalleryCounting
