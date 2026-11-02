import Guralnick.ParabolicWeb
import Guralnick.CanonicalSchur

/-!
# Integral auxiliary split--merge chains

A step is the actual inclusion through the common finite parabolic followed
by the actual integral merge. The two-step and three-step chains define the
full-spherical and one-retained-line auxiliary vectors. Cleared products,
bar invariance and cleared canonical positivity are proved from the general
parabolic and Hecke literature inputs. No auxiliary canonicality or special
coordinate formula is assumed in these constructions.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace Guralnick.CanonicalChains

open scoped BigOperators
open Hecke ParabolicWeb Positivity

variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)

def meet (I J : Index n) : Index n :=
  ⟨I.val ∩ J.val, by
    intro h
    apply I.property
    apply Finset.eq_univ_of_forall
    intro i
    exact Finset.mem_of_mem_inter_left (h ▸ Finset.mem_univ i)⟩

def step (I J : Index n) :
    SphericalMaps.spherical (symmetrizer K D I) →ₗ[R]
      SphericalMaps.spherical (symmetrizer K D J) :=
  (Classical.choice (L.merge_exists (meet I J) J Finset.inter_subset_right)).linear.comp
    (Submodule.inclusion (L.inclusion (meet I J) I Finset.inter_subset_left))

theorem step_cleared (I J : Index n)
    (x : SphericalMaps.spherical (symmetrizer K D I)) :
    scalar D (meet I J) • (step K D L I J x).val =
      symmetrizer K D J * x.val := by
  exact SphericalMaps.merge_cleared
    (Classical.choice (L.merge_exists (meet I J) J Finset.inter_subset_right)) _
    (L.absorption (meet I J) J Finset.inter_subset_right)
    (Submodule.inclusion (L.inclusion (meet I J) I Finset.inter_subset_left) x)

/-- An arbitrary finite path of spherical boundaries. Every edge is the
integral split through the common facet followed by the merge. -/
inductive Chain : Index n → Index n → Type
  | nil (I : Index n) : Chain I I
  | snoc {I J : Index n} (p : Chain I J) (T : Index n) : Chain I T

namespace Chain

variable {I J : Index n}

def linear : {I J : Index n} → Chain I J →
    SphericalMaps.spherical (symmetrizer K D I) →ₗ[R]
      SphericalMaps.spherical (symmetrizer K D J)
  | _, _, .nil _ => LinearMap.id
  | _, _, .snoc (J := J) p T => (step K D L J T).comp (linear p)

def raw (p : Chain I J) : Hecke.Algebra n :=
  (linear K D L p (SphericalMaps.generator (symmetrizer K D I) 1)).val

def denominator : {I J : Index n} → Chain I J → R
  | _, _, .nil _ => 1
  | _, _, .snoc (J := J) p T => denominator p * scalar D (meet J T)

def numerator : {I J : Index n} → Chain I J → Hecke.Algebra n
  | _, _, .nil I => symmetrizer K D I
  | _, _, .snoc p T => symmetrizer K D T * numerator p

/-- The normalization exponent before subtracting the endpoint length.
It is computed from the actual longest finite-parabolic elements. -/
def weight : {I J : Index n} → Chain I J → ℤ
  | _, _, .nil I => c.system.length (D I).longest.val
  | _, _, .snoc (J := J) p T =>
      weight p + c.system.length (D T).longest.val - c.system.length (D (meet J T)).longest.val

def vertices : {I J : Index n} → Chain I J → List (Index n)
  | _, _, .nil I => [I]
  | _, _, .snoc p T => vertices p ++ [T]

theorem raw_nil (I : Index n) : raw K D L (.nil I) = symmetrizer K D I := by
  simp [raw, linear, SphericalMaps.generator_val]

theorem raw_snoc {I J : Index n} (p : Chain I J) (T : Index n) :
    raw K D L (.snoc p T) =
      (step K D L J T (linear K D L p
        (SphericalMaps.generator (symmetrizer K D I) 1))).val := by
  simp only [raw, linear, LinearMap.comp_apply]

theorem cleared {I J : Index n} (p : Chain I J) :
    denominator D p • raw K D L p = numerator K D p := by
  induction p with
  | nil => simp [denominator, numerator, raw_nil]
  | @snoc J p T ih =>
      rw [denominator, mul_smul, raw_snoc, step_cleared, ← mul_smul_comm]
      change symmetrizer K D T * (denominator D p • raw K D L p) = _
      rw [ih]
      simp only [numerator]

end Chain

def twoResult (I₀ I₁ I₂ : Index n) :
    SphericalMaps.spherical (symmetrizer K D I₂) :=
  step K D L I₁ I₂
    (step K D L I₀ I₁ (SphericalMaps.generator (symmetrizer K D I₀) 1))

def threeResult (I₀ I₁ I₂ I₃ : Index n) :
    SphericalMaps.spherical (symmetrizer K D I₃) :=
  step K D L I₂ I₃ (twoResult K D L I₀ I₁ I₂)

def twoDenominator (I₀ I₁ I₂ : Index n) : R :=
  scalar D (meet I₀ I₁) * scalar D (meet I₁ I₂)

def threeDenominator (I₀ I₁ I₂ I₃ : Index n) : R :=
  twoDenominator D I₀ I₁ I₂ * scalar D (meet I₂ I₃)

theorem two_cleared (I₀ I₁ I₂ : Index n) :
    twoDenominator D I₀ I₁ I₂ • (twoResult K D L I₀ I₁ I₂).val =
      symmetrizer K D I₂ * symmetrizer K D I₁ * symmetrizer K D I₀ := by
  unfold twoDenominator twoResult
  rw [mul_smul, step_cleared, ← mul_smul_comm, step_cleared]
  simp only [SphericalMaps.generator_val, mul_one, mul_assoc]

theorem three_cleared (I₀ I₁ I₂ I₃ : Index n) :
    threeDenominator D I₀ I₁ I₂ I₃ • (threeResult K D L I₀ I₁ I₂ I₃).val =
      symmetrizer K D I₃ * symmetrizer K D I₂ *
        symmetrizer K D I₁ * symmetrizer K D I₀ := by
  unfold threeDenominator threeResult
  rw [mul_smul, step_cleared, ← mul_smul_comm, two_cleared]
  simp only [mul_assoc]

include K L

theorem two_denominator_ne_zero (I₀ I₁ I₂ : Index n) :
    twoDenominator D I₀ I₁ I₂ ≠ 0 :=
  mul_ne_zero (L.scalar_ne_zero _) (L.scalar_ne_zero _)

theorem three_denominator_ne_zero (I₀ I₁ I₂ I₃ : Index n) :
    threeDenominator D I₀ I₁ I₂ I₃ ≠ 0 :=
  mul_ne_zero (two_denominator_ne_zero K D L _ _ _) (L.scalar_ne_zero _)

theorem two_denominator_bar (I₀ I₁ I₂ : Index n) :
    LaurentPolynomial.invert (twoDenominator D I₀ I₁ I₂) =
      twoDenominator D I₀ I₁ I₂ := by
  simp only [twoDenominator, map_mul, L.scalar_bar]

theorem three_denominator_bar (I₀ I₁ I₂ I₃ : Index n) :
    LaurentPolynomial.invert (threeDenominator D I₀ I₁ I₂ I₃) =
      threeDenominator D I₀ I₁ I₂ I₃ := by
  simp only [threeDenominator, map_mul, two_denominator_bar K D L, L.scalar_bar]

theorem two_bar (I₀ I₁ I₂ : Index n) :
    K.bar (twoResult K D L I₀ I₁ I₂).val = (twoResult K D L I₀ I₁ I₂).val := by
  apply bar_of_cleared K (two_denominator_ne_zero K D L _ _ _)
    (two_denominator_bar K D L _ _ _)
  rw [two_cleared]
  simp only [map_mul, symmetrizer, K.bar_canonical]

theorem three_bar (I₀ I₁ I₂ I₃ : Index n) :
    K.bar (threeResult K D L I₀ I₁ I₂ I₃).val =
      (threeResult K D L I₀ I₁ I₂ I₃).val := by
  apply bar_of_cleared K (three_denominator_ne_zero K D L _ _ _ _)
    (three_denominator_bar K D L _ _ _ _)
  rw [three_cleared]
  simp only [map_mul, symmetrizer, K.bar_canonical]

theorem two_cleared_nonnegative (P : PositivityInput K) (I₀ I₁ I₂ : Index n)
    (w : AffinePermutation n) :
    Nonnegative (twoDenominator D I₀ I₁ I₂ *
      K.canonical.repr (twoResult K D L I₀ I₁ I₂).val w) := by
  have h := congrArg (fun x => K.canonical.repr x w) (two_cleared K D L I₀ I₁ I₂)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  rw [h]
  exact canonical_product_three_nonnegative K P _ _ _ w

theorem three_cleared_nonnegative (P : PositivityInput K) (I₀ I₁ I₂ I₃ : Index n)
    (w : AffinePermutation n) :
    Nonnegative (threeDenominator D I₀ I₁ I₂ I₃ *
      K.canonical.repr (threeResult K D L I₀ I₁ I₂ I₃).val w) := by
  exact cleared_coordinates_nonnegative K P
    (D I₃).longest.val (D I₂).longest.val (D I₁).longest.val (D I₀).longest.val
    (three_cleared K D L I₀ I₁ I₂ I₃) w

/-- Both boundary eigenspaces are preserved by an integral auxiliary chain. -/
theorem two_mem_corner (I₀ I₁ I₂ : Index n) :
    (twoResult K D L I₀ I₁ I₂).val ∈ CanonicalSchur.corner I₂ I₀ := by
  apply CanonicalSchur.corner_of_cleared K (two_denominator_ne_zero K D L _ _ _)
  rw [two_cleared]
  constructor
  · intro i hi
    calc
      H i * (symmetrizer K D I₂ * symmetrizer K D I₁ * symmetrizer K D I₀) =
          (H i * symmetrizer K D I₂) * symmetrizer K D I₁ * symmetrizer K D I₀ := by
            simp only [mul_assoc]
      _ = (LaurentPolynomial.T (-1) : R) •
          (symmetrizer K D I₂ * symmetrizer K D I₁ * symmetrizer K D I₀) := by
            rw [L.left_eigen I₂ i hi, smul_mul_assoc, smul_mul_assoc]
  · intro i hi
    calc
      (symmetrizer K D I₂ * symmetrizer K D I₁ * symmetrizer K D I₀) * H i =
          (symmetrizer K D I₂ * symmetrizer K D I₁) * (symmetrizer K D I₀ * H i) :=
            mul_assoc _ _ _
      _ = (LaurentPolynomial.T (-1) : R) •
          (symmetrizer K D I₂ * symmetrizer K D I₁ * symmetrizer K D I₀) := by
            rw [L.right_eigen I₀ i hi, mul_smul_comm]

theorem three_mem_corner (I₀ I₁ I₂ I₃ : Index n) :
    (threeResult K D L I₀ I₁ I₂ I₃).val ∈ CanonicalSchur.corner I₃ I₀ := by
  apply CanonicalSchur.corner_of_cleared K (three_denominator_ne_zero K D L _ _ _ _)
  rw [three_cleared]
  constructor
  · intro i hi
    calc
      H i * (symmetrizer K D I₃ * symmetrizer K D I₂ *
          symmetrizer K D I₁ * symmetrizer K D I₀) =
          (H i * symmetrizer K D I₃) * symmetrizer K D I₂ *
            symmetrizer K D I₁ * symmetrizer K D I₀ := by simp only [mul_assoc]
      _ = (LaurentPolynomial.T (-1) : R) •
          (symmetrizer K D I₃ * symmetrizer K D I₂ *
            symmetrizer K D I₁ * symmetrizer K D I₀) := by
            rw [L.left_eigen I₃ i hi, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
  · intro i hi
    calc
      (symmetrizer K D I₃ * symmetrizer K D I₂ *
          symmetrizer K D I₁ * symmetrizer K D I₀) * H i =
          (symmetrizer K D I₃ * symmetrizer K D I₂ * symmetrizer K D I₁) *
            (symmetrizer K D I₀ * H i) := mul_assoc _ _ _
      _ = (LaurentPolynomial.T (-1) : R) •
          (symmetrizer K D I₃ * symmetrizer K D I₂ *
            symmetrizer K D I₁ * symmetrizer K D I₀) := by
            rw [L.right_eigen I₀ i hi, mul_smul_comm]

/-- Auxiliary canonicality is derived from proper-coordinate degree tests
at maximal double-coset indices. Neither Bruhat maximality nor the canonical
identity itself is an input. The coordinate tests are original obligations. -/
theorem three_canonical_of_coordinates (P : PositivityInput K)
    (C : CanonicalSchur.Compatibility K) (I₀ I₁ I₂ I₃ : Index n)
    (t : AffinePermutation n)
    (hleading : K.standard.repr (threeResult K D L I₀ I₁ I₂ I₃).val t = 1)
    (hproper : ∀ w, CanonicalSchur.DoubleMaximal c I₃ I₀ w → w ≠ t →
      LowerBound (K.standard.repr (threeResult K D L I₀ I₁ I₂ I₃).val w) 1) :
    (threeResult K D L I₀ I₁ I₂ I₃).val = K.canonical t := by
  refine CanonicalBasis.canonical_single_of_positive_canonical_support
    K.standard K.canonical (threeResult K D L I₀ I₁ I₂ I₃).val (threeDenominator D I₀ I₁ I₂ I₃) t
    (three_denominator_ne_zero K D L _ _ _ _) K.canonical_diagonal
    P.standard_nonnegative
    (fun w => canonical_coordinate_barSymmetric K (three_bar K D L _ _ _ _) w)
    (three_cleared_nonnegative K D L P I₀ I₁ I₂ I₃) hleading ?_
  intro w hw hwt
  apply hproper w _ hwt
  exact C.canonical_support I₃ I₀ _ (three_mem_corner K D L _ _ _ _) w
    (Finsupp.mem_support_iff.mp hw)

/-- Full-spherical multiplicity one, including existence of the canonical
term. Counts need only be tested at maximal indices in the actual standard
support; ordinary nonmaximal coordinates are not confused with Schur ones. -/
theorem two_multiplicity_one_of_coordinates (P : PositivityInput K)
    (C : CanonicalSchur.Compatibility K) (I₀ I₁ I₂ : Index n)
    (hcoords : ∀ w, CanonicalSchur.DoubleMaximal c I₂ I₀ w →
      K.standard.repr (twoResult K D L I₀ I₁ I₂).val w ≠ 0 →
      LowerBound (K.standard.repr (twoResult K D L I₀ I₁ I₂).val w) 0 ∧
      (K.standard.repr (twoResult K D L I₀ I₁ I₂).val w) 0 = 1)
    (w : AffinePermutation n) (hwmax : CanonicalSchur.DoubleMaximal c I₂ I₀ w)
    (hwne : K.standard.repr (twoResult K D L I₀ I₁ I₂).val w ≠ 0) :
    K.canonical.repr (twoResult K D L I₀ I₁ I₂).val w = 1 := by
  classical
  let x := (twoResult K D L I₀ I₁ I₂).val
  let S := insert w (K.canonical.repr x).support
  have hsupport := CanonicalBasis.canonical_support_subset_standard K.standard K.canonical x
    (twoDenominator D I₀ I₁ I₂) (two_denominator_ne_zero K D L _ _ _)
    K.canonical_diagonal P.standard_nonnegative
    (fun z _ => two_cleared_nonnegative K D L P _ _ _ z)
  have hdata : ∀ z ∈ S, LowerBound (K.standard.repr x z) 0 ∧
      (K.standard.repr x z) 0 = 1 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzw | hz
    · subst z
      exact hcoords w hwmax hwne
    · apply hcoords z
      · exact C.canonical_support I₂ I₀ x (two_mem_corner K D L _ _ _) z
          (Finsupp.mem_support_iff.mp hz)
      · exact Finsupp.mem_support_iff.mp (hsupport hz)
  apply CanonicalBasis.all_multiplicities_one S (twoDenominator D I₀ I₁ I₂)
    (fun z => K.canonical.repr x z) (fun y z => K.standard.repr (K.canonical z) y)
    (fun z => K.standard.repr x z) (two_denominator_ne_zero K D L _ _ _)
    (fun z _ => K.canonical_diagonal z)
    (fun y _ z _ => P.standard_nonnegative y z)
    (fun y _ z _ hyz => K.canonical_lower y z (Ne.symm hyz))
    (fun z _ => canonical_coordinate_barSymmetric K (two_bar K D L _ _ _) z)
    (fun z _ => two_cleared_nonnegative K D L P _ _ _ z)
    (fun z _ => CanonicalBasis.coordinate_expansion_on K.standard K.canonical x S
      (Finset.subset_insert _ _) z)
    (fun z hz => (hdata z hz).1) (fun z hz => (hdata z hz).2) w (Finset.mem_insert_self _ _)

/-- A standard finite maximal parabolic: omit one affine node. -/
def omitNode (i : Fin n) : Index n :=
  ⟨Finset.univ.erase i, by
    intro h
    have hi := Finset.mem_univ i
    rw [← h] at hi
    exact Finset.notMem_erase i _ hi⟩

def source (hn : 0 < n) : Index n := omitNode ⟨0, hn⟩

def retainedLine (hn : 0 < n) : Index n :=
  ⟨(source hn).val.filter (fun i => i.val ≠ 1), by
    intro h
    apply (source hn).property
    apply Finset.eq_univ_of_forall
    intro i
    exact (Finset.mem_filter.mp (h ▸ Finset.mem_univ i)).1⟩

def twoRow (hn : 0 < n) (f : Fin n) : Index n := meet (source hn) (omitNode f)

/-- The one-retained-line integral web in §6, read as left multiplication
on right ideals. Its numerator order is the reverse of the manuscript's
right-module notation, as for the main six-map web. -/
def oneLine (hn : 0 < n) (j f : Fin n) : Hecke.Algebra n :=
  (threeResult K D L (source hn) (omitNode j) (retainedLine hn) (twoRow hn f)).val

/-- The full-spherical integral web in §7. -/
def spherical (hn : 0 < n) (s : Fin n) : Hecke.Algebra n :=
  (twoResult K D L (source hn) (omitNode s) (source hn)).val

theorem oneLine_cleared (hn : 0 < n) (j f : Fin n) :
    threeDenominator D (source hn) (omitNode j) (retainedLine hn) (twoRow hn f) •
        oneLine K D L hn j f =
      symmetrizer K D (twoRow hn f) * symmetrizer K D (retainedLine hn) *
        symmetrizer K D (omitNode j) * symmetrizer K D (source hn) :=
  three_cleared K D L _ _ _ _

theorem spherical_cleared (hn : 0 < n) (s : Fin n) :
    twoDenominator D (source hn) (omitNode s) (source hn) • spherical K D L hn s =
      symmetrizer K D (source hn) * symmetrizer K D (omitNode s) *
        symmetrizer K D (source hn) := two_cleared K D L _ _ _

/-- The actual general path used by the one-line web. -/
def oneLineChain (hn : 0 < n) (j f : Fin n) :
    Chain (source hn) (twoRow hn f) :=
  ((Chain.nil (source hn)).snoc (omitNode j)).snoc (retainedLine hn) |>.snoc (twoRow hn f)

def sphericalChain (hn : 0 < n) (s : Fin n) : Chain (source hn) (source hn) :=
  ((Chain.nil (source hn)).snoc (omitNode s)).snoc (source hn)

theorem oneLine_eq_chain (hn : 0 < n) (j f : Fin n) :
    oneLine K D L hn j f = Chain.raw K D L (oneLineChain hn j f) := by
  simp only [oneLine, oneLineChain, Chain.raw, Chain.linear, threeResult, twoResult,
    LinearMap.comp_apply, LinearMap.id_apply]

theorem spherical_eq_chain (hn : 0 < n) (s : Fin n) :
    spherical K D L hn s = Chain.raw K D L (sphericalChain hn s) := by
  simp only [spherical, sphericalChain, Chain.raw, Chain.linear, twoResult,
    LinearMap.comp_apply, LinearMap.id_apply]

omit K L in
theorem main_meet_source (m : ℕ) :
    meet (Family.source m) (Family.cyclic m) = Family.output m := by
  apply Subtype.ext
  rfl

omit K L in
theorem main_meet_cyclic (m : ℕ) :
    meet (Family.cyclic m) (Family.middle m) = Family.common m := by
  apply Subtype.ext
  rfl

omit K L in
theorem main_meet_middle (m : ℕ) :
    meet (Family.middle m) (Family.output m) = Family.common m := by
  apply Subtype.ext
  ext i
  change (i ∈ Family.middleSet m ∩ Family.outputSet m) ↔ i ∈ Family.commonSet m
  simp only [Family.outputSet, Family.commonSet, Finset.mem_inter]
  constructor
  · rintro ⟨hm, hs, hc⟩
    exact ⟨hc, hm⟩
  · rintro ⟨hc, hm⟩
    exact ⟨hm, Family.middle_subset_source m hm, hc⟩

def mainChain (m : ℕ) : Chain (Family.source m) (Family.output m) :=
  (((Chain.nil (Family.source m)).snoc (Family.cyclic m)).snoc
    (Family.middle m)).snoc (Family.output m)

omit K D L in
/-- Its facets are exactly the three facets of the manuscript's main web. -/
theorem main_vertices (m : ℕ) :
    Chain.vertices (mainChain m) =
      [Family.source m, Family.cyclic m, Family.middle m, Family.output m] := by
  simp only [mainChain, Chain.vertices, List.append_assoc, List.cons_append, List.nil_append]

end Guralnick.CanonicalChains

namespace Guralnick.CanonicalChains

open Hecke ParabolicWeb
variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
variable (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)

/-- The previously defined six-map element is the evaluation of the general
chain. The proof uses integral scalar cancellation, so it does not depend on
which existence witnesses supplied the merge maps. -/
theorem main_raw_eq_chain : Family.raw K D L = Chain.raw K D L (mainChain m) := by
  apply scalar_cancel K (Family.denominator_ne_zero K D L)
  rw [Family.raw_cleared]
  have hd : Chain.denominator D (mainChain m) =
      scalar D (Family.output m) * scalar D (Family.common m)^2 := by
    simp only [mainChain, Chain.denominator, main_meet_source,
      main_meet_cyclic, main_meet_middle, one_mul, pow_two]
    ring
  rw [← hd, Chain.cleared]
  simp only [mainChain, Chain.numerator, mul_assoc]

end Guralnick.CanonicalChains
