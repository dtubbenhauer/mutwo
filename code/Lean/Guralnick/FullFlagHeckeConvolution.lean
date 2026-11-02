import Guralnick.PolynomialFullGallery
import Guralnick.PolynomialFlagConvolution
import Guralnick.ParabolicFlagStabilizer
import Guralnick.ParabolicStandardSum
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Full-flag affine Hecke convolution in the polynomial model

The external input is the full-flag orbit classification and binary Hecke
convolution realization. Relative position uses an actual common change of
basis over k[t,t⁻¹], and the normalized standard coordinate supplies the
kernel. No partial-flag normalization, parabolic fiber count, or arbitrary
chain formula occurs among the input fields.

The source is Lusztig, Aperiodicity in quantum affine gl_n, §§1.3–1.9
(especially Lemma 1.5 and §1.7), with the full-flag Hecke identification in
Cui, §7.1, Lemma 7.1. The standard generator convention is Q=v⁻²,
H_w=v^length(w) T_w. Here Q=p² and v=1/p.
-/
noncomputable section
namespace Guralnick.FullFlagHeckeConvolution
open Hecke ParabolicWeb CanonicalChains PolynomialFullGallery PolynomialsFromCounts
open scoped BigOperators Classical
variable {n : ℕ} [NeZero n] {k : Type} [Field k]

/-- Literal simultaneous polynomial Laurent coordinates of a full-flag pair.
The target is the left endpoint of the kernel, and the source the right. -/
def RelativePosition (target source : FullFlag k n) (w : AffinePermutation n) : Prop :=
  ∃ g : PolynomialLattice.Ambient k n ≃ₗ[LaurentPolynomial k] PolynomialLattice.Ambient k n,
    (∀ i, PolynomialAffineCoordinates.mapModule k n g
      (PolynomialAffineCoordinates.coordinateModule k n i.val.val) = (target.node i).module) ∧
    (∀ i, PolynomialAffineCoordinates.mapModule k n g
      (PolynomialAffineCoordinates.mapModule k n (PolynomialAffineCoordinates.windowEquiv k n w)
        (PolynomialAffineCoordinates.coordinateModule k n i.val.val)) = (source.node i).module)

/-- Equality of polynomial submodules can be checked after an invertible
change of Laurent coordinates. -/
theorem mapModule_injective
    (g : PolynomialLattice.Ambient k n ≃ₗ[LaurentPolynomial k] PolynomialLattice.Ambient k n) :
    Function.Injective (PolynomialAffineCoordinates.mapModule k n g) := by
  intro M N h
  apply le_antisymm
  · intro x hx
    have hm : g x ∈ PolynomialAffineCoordinates.mapModule k n g M := ⟨x,hx,rfl⟩
    rw [h] at hm
    obtain ⟨y,hy,he⟩ := hm
    exact g.injective he ▸ hy
  · intro x hx
    have hm : g x ∈ PolynomialAffineCoordinates.mapModule k n g N := ⟨x,hx,rfl⟩
    rw [←h] at hm
    obtain ⟨y,hy,he⟩ := hm
    exact g.injective he ▸ hy

/-- Parabolic agreement is derived from the actual cut stabilizer theorem;
it is not an orbit-theorem assumption. -/
theorem forget_eq_iff (c : WindowCoxeter n) (I : Index n)
    {target source : FullFlag k n} {w : AffinePermutation n}
    (h : RelativePosition target source w) :
    forget I source=forget I target ↔ w∈subgroup c I := by
  obtain ⟨g,ht,hs⟩ := h
  rw [ParabolicFlagStabilizer.mem_subgroup_iff_cuts]
  constructor
  · intro he a ha
    have ham : a∈LatticeFlags.retained I := Finset.mem_compl.mpr ha
    let i : {i // i∈LatticeFlags.retained (fullIndex n)} :=
      ⟨a,retained_subset_full I ham⟩
    have hn := congrArg (fun F : PolynomialFlags.Flag k n (LatticeFlags.retained I) =>
      (F.node ⟨a,ham⟩).module) he
    change (source.node i).module=(target.node i).module at hn
    rw [←hs i,←ht i] at hn
    exact (ParabolicFlagStabilizer.coordinateModule_fixed_iff k a w).mp
      (mapModule_injective g hn)
  · intro hw
    apply PolynomialFlags.Flag.ext
    funext i
    apply PolynomialLattice.Lattice.ext
    let j : {i // i∈LatticeFlags.retained (fullIndex n)} :=
      ⟨i.val,retained_subset_full I i.property⟩
    change (source.node j).module=(target.node j).module
    rw [←hs j,←ht j]
    apply congrArg (PolynomialAffineCoordinates.mapModule k n g)
    exact (ParabolicFlagStabilizer.coordinateModule_fixed_iff k i.val w).mpr
      (hw i.val (Finset.mem_compl.mp i.property))

/-- Full-flag orbit classification, restricted to the degree-zero component.
The group element is the actual balanced affine window. -/
def OrbitClassification (k : Type) [Field k] (n : ℕ) [NeZero n] : Prop :=
  ∀ target source : FullFlag k n, ∃! w : AffinePermutation n, RelativePosition target source w

def position (O : OrbitClassification k n) (target source : FullFlag k n) : AffinePermutation n :=
  Classical.choose (O target source)

theorem position_spec (O : OrbitClassification k n) (target source : FullFlag k n) :
    RelativePosition target source (position O target source) :=
  (Classical.choose_spec (O target source)).1

theorem position_eq (O : OrbitClassification k n) {target source : FullFlag k n}
    {w : AffinePermutation n} (h : RelativePosition target source w) :
    position O target source=w :=
  ((Classical.choose_spec (O target source)).2 w h).symm

variable {c : WindowCoxeter n} (K : KLRealization c) (p : ℕ) [Fact p.Prime] (hp : p.Prime)

/-- The standard coordinate evaluated as a full-flag kernel. Multiplication
by v^length converts an H-coordinate to a characteristic-orbit coordinate. -/
def value (O : OrbitClassification (GaloisField p 2) n) (x : Hecke.Algebra n)
    (target source : FullFlag (GaloisField p 2) n) : ℚ :=
  ((primeUnit p hp)^(c.system.length (position O target source) : ℤ)).val *
    specialize p hp (K.standard.repr x (position O target source))

/-- Source-level affine full-flag realization. Its sole multiplication
statement is binary convolution; every parabolic/chain formula is derived. -/
structure Input : Prop where
  orbits : OrbitClassification (GaloisField p 2) n
  convolution : ∀ (x y : Hecke.Algebra n) (target source : FullFlag (GaloisField p 2) n),
    value K p hp orbits (x*y) target source =
      ∑ᶠ middle : FullFlag (GaloisField p 2) n,
        value K p hp orbits x target middle * value K p hp orbits y middle source

variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)
include L

theorem symmetrizer_coordinate (I : Index n) (w : AffinePermutation n) :
    K.standard.repr (symmetrizer K D I) w =
      if w∈subgroup c I then
        LaurentPolynomial.T ((c.system.length (D I).longest.val : ℤ)-c.system.length w) else 0 := by
  letI := (D I).finite
  letI := Fintype.ofFinite (subgroup c I)
  rw [L.standard_sum]
  exact ParabolicStandardSum.standard_coordinate K (subgroup c I) _ w

/-- A finite canonical symmetrizer is exactly the retained-cut indicator,
with its one constant normalization factor. -/
theorem value_symmetrizer (O : OrbitClassification (GaloisField p 2) n)
    (I : Index n) (target source : FullFlag (GaloisField p 2) n) :
    value K p hp O (symmetrizer K D I) target source =
      if forget I source=forget I target then
        ((primeUnit p hp)^(c.system.length (D I).longest.val : ℤ)).val else 0 := by
  classical
  unfold value
  rw [symmetrizer_coordinate K D L]
  have he := forget_eq_iff c I (position_spec O target source)
  by_cases h : forget I source=forget I target
  · rw [if_pos h,if_pos (he.mp h)]
    simp only [specialize,LaurentPolynomial.eval₂_T]
    rw [←Units.val_mul,←zpow_add]
    congr 2
    ring
  · rw [if_neg h,if_neg (fun hw => h (he.mpr hw)),map_zero,mul_zero]

omit L in
theorem value_smul (O : OrbitClassification (GaloisField p 2) n) (r : R)
    (x : Hecke.Algebra n) (target source : FullFlag (GaloisField p 2) n) :
    value K p hp O (r • x) target source =
      specialize p hp r * value K p hp O x target source := by
  simp only [value,map_smul,Finsupp.smul_apply,smul_eq_mul,map_mul]
  ring

omit L in
/-- A finite predicate may be summed as its subtype; no compiled cardinal
oracle or infinite-sum convention is used in this calculation. -/
theorem finsum_indicator {α : Type} (P : α → Prop) [Finite {a // P a}]
    (f : α → ℚ) :
    letI := Fintype.ofFinite {a // P a}
    (∑ᶠ a, if P a then f a else 0) = ∑ a : {a // P a}, f a.val := by
  classical
  letI := Fintype.ofFinite {a // P a}
  let S : Finset α := Finset.univ.image (fun a : {a // P a} => a.val)
  have hS (a : α) : a∈S ↔ P a := by simp [S]
  rw [finsum_eq_sum_of_support_subset _ (s := S) (by
    intro a ha
    apply (hS a).mpr
    by_contra hn
    exact ha (if_neg hn))]
  rw [Finset.sum_subtype S hS]
  apply Finset.sum_congr rfl
  intro a _
  exact if_pos a.property

/-- Squaring the actual canonical parabolic symmetrizer counts its literal
full-flag lift fiber. This is the elementary bridge used to derive the
Poincare fiber cardinality. -/
theorem symmetrizer_square_count (C : Input K p hp) (I : Index n)
    (F : FullFlag (GaloisField p 2) n) :
    specialize p hp (scalar D I) *
        ((primeUnit p hp)^(c.system.length (D I).longest.val : ℤ)).val =
      (((primeUnit p hp)^(c.system.length (D I).longest.val : ℤ)).val)^2 *
        (Nat.card (Lift (forget I F)) : ℚ) := by
  classical
  letI : Finite {a : FullFlag (GaloisField p 2) n // forget I a=forget I F} :=
    inferInstanceAs (Finite (Lift (forget I F)))
  letI : Fintype {a : FullFlag (GaloisField p 2) n // forget I a=forget I F} :=
    Fintype.ofFinite _
  have h := C.convolution (symmetrizer K D I) (symmetrizer K D I) F F
  rw [L.absorption I I (Finset.Subset.refl I.val),value_smul,
    value_symmetrizer K p hp D L,if_pos rfl] at h
  rw [h]
  have hs : (∑ᶠ middle : FullFlag (GaloisField p 2) n,
      value K p hp C.orbits (symmetrizer K D I) F middle *
        value K p hp C.orbits (symmetrizer K D I) middle F) =
      ∑ᶠ middle : FullFlag (GaloisField p 2) n,
        if forget I middle=forget I F then
          (((primeUnit p hp)^(c.system.length (D I).longest.val : ℤ)).val)^2 else 0 := by
    apply finsum_congr
    intro middle
    rw [value_symmetrizer K p hp D L,value_symmetrizer K p hp D L]
    by_cases he : forget I middle=forget I F
    · rw [if_pos he,if_pos he.symm,if_pos he,pow_two]
    · rw [if_neg he,if_neg (Ne.symm he),if_neg he,zero_mul]
  rw [hs,finsum_indicator]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card]
  change (Nat.card (Lift (forget I F)) : ℚ) * _ = _
  ring

#print axioms forget_eq_iff
#print axioms value_symmetrizer
#print axioms symmetrizer_square_count
end Guralnick.FullFlagHeckeConvolution
