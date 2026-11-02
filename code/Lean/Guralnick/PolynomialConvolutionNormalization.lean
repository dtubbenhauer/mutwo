import Guralnick.PolynomialFullGallery
import Guralnick.PolynomialsFromCounts

/-!
# Elementary normalization of polynomial flag convolution

The two counts in `normalized_raw_of_fullGallery_count` are counts of the
actual full and partial flag-gallery types. The theorem separates the
full-flag convolution calculation and the flag-lift bijection from the
purely algebraic cancellation of finite-parabolic Poincare factors.
-/
noncomputable section
namespace Guralnick.PolynomialConvolutionNormalization
open scoped BigOperators
open Hecke ParabolicWeb CanonicalChains PolynomialsFromCounts

variable {n : ℕ} {c : WindowCoxeter n}
variable (D : ∀ I : Index n, LongestData c I)

/-- Sum of longest-element lengths at all vertices, including both ends. -/
def vertexWeight : {I J : Index n} → Chain I J → ℤ
  | _, _, .nil I => c.system.length (D I).longest.val
  | _, _, .snoc path T => vertexWeight path + c.system.length (D T).longest.val

/-- Sum of longest-element lengths of the common facets at all steps. -/
def meetWeight : {I J : Index n} → Chain I J → ℤ
  | _, _, .nil _ => 0
  | _, _, .snoc (J := J) path T =>
      meetWeight path + c.system.length (D (meet J T)).longest.val

/-- The actual common finite parabolic at each successive step. -/
def meetVertices : {I J : Index n} → Chain I J → List (Index n)
  | _, _, .nil _ => []
  | _, _, .snoc (J := J) path T => meetVertices path ++ [meet J T]

theorem meetWeight_eq_sum {I J : Index n} (path : Chain I J) :
    meetWeight D path =
      ((meetVertices path).map (fun I => (c.system.length (D I).longest.val : ℤ))).sum := by
  induction path with
  | nil => simp [meetWeight,meetVertices]
  | snoc path T ih => simp [meetWeight,meetVertices,ih]

theorem weight_eq {I J : Index n} (path : Chain I J) :
    Chain.weight D path = vertexWeight D path - meetWeight D path := by
  induction path with
  | nil => simp only [Chain.weight,vertexWeight,meetWeight,sub_zero]
  | snoc path T ih =>
      simp only [Chain.weight,vertexWeight,meetWeight,ih]
      ring

theorem vertexWeight_eq_sum {I J : Index n} (path : Chain I J) :
    vertexWeight D path =
      ((Chain.vertices path).map (fun I => (c.system.length (D I).longest.val : ℤ))).sum := by
  induction path with
  | nil => simp [vertexWeight,Chain.vertices]
  | snoc path T ih => simp [vertexWeight,Chain.vertices,ih]

/-- Actual Poincare sum over the finite subgroup, at field size p². -/
def PoincareValue (p : ℕ) (I : Index n) : ℚ :=
  letI : Finite (subgroup c I) := (D I).finite
  letI := Fintype.ofFinite (subgroup c I)
  ∑ w : subgroup c I, ((p : ℚ)^2)^(c.system.length w.val)

theorem poincareValue_pos (p : ℕ) (hp : p.Prime) (I : Index n) :
    0 < PoincareValue D p I := by
  letI : Finite (subgroup c I) := (D I).finite
  letI := Fintype.ofFinite (subgroup c I)
  unfold PoincareValue
  apply Finset.sum_pos
  · intro w _
    exact pow_pos (sq_pos_of_pos (by exact_mod_cast hp.pos)) _
  · exact Finset.univ_nonempty

theorem poincareValue_ne_zero (p : ℕ) (hp : p.Prime) (I : Index n) :
    PoincareValue D p I ≠ 0 := ne_of_gt (poincareValue_pos D p hp I)

/-- The finite symmetrizer scalar is v^ell(wI) times its Poincare sum. -/
theorem scalar_specialize (p : ℕ) (hp : p.Prime) (I : Index n) :
    specialize p hp (scalar D I) =
      ((primeUnit p hp) ^ (c.system.length (D I).longest.val : ℤ)).val *
        PoincareValue D p I := by
  letI : Finite (subgroup c I) := (D I).finite
  letI := Fintype.ofFinite (subgroup c I)
  simp only [scalar,PoincareValue,map_sum,specialize,LaurentPolynomial.eval₂_T,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [show (c.system.length (D I).longest.val : ℤ) - 2 * c.system.length w.val =
      (c.system.length (D I).longest.val : ℤ) + (-2) * (c.system.length w.val : ℤ) by ring,
    zpow_add,zpow_mul,zpow_natCast]
  simp only [zpow_natCast,Units.val_mul,Units.val_pow_eq_pow_val,primeUnit_parameter]

/-- Product of the Poincare sums at the actual successive common facets. -/
def poincareProduct (p : ℕ) : {I J : Index n} → Chain I J → ℚ
  | _, _, .nil _ => 1
  | _, _, .snoc (J := J) path T => poincareProduct p path * PoincareValue D p (meet J T)

theorem poincareProduct_eq_prod (p : ℕ) {I J : Index n} (path : Chain I J) :
    poincareProduct D p path = ((meetVertices path).map (PoincareValue D p)).prod := by
  induction path with
  | nil => simp [poincareProduct,meetVertices]
  | snoc path T ih => simp [poincareProduct,meetVertices,ih]

theorem poincareProduct_pos (p : ℕ) (hp : p.Prime) {I J : Index n} (path : Chain I J) :
    0 < poincareProduct D p path := by
  induction path with
  | nil => simp only [poincareProduct]; norm_num
  | snoc path T ih =>
      rw [poincareProduct]
      exact mul_pos ih (poincareValue_pos D p hp _)

theorem poincareProduct_ne_zero (p : ℕ) (hp : p.Prime) {I J : Index n} (path : Chain I J) :
    poincareProduct D p path ≠ 0 := ne_of_gt (poincareProduct_pos D p hp path)

theorem denominator_specialize (p : ℕ) (hp : p.Prime) {I J : Index n} (path : Chain I J) :
    specialize p hp (Chain.denominator D path) =
      ((primeUnit p hp) ^ meetWeight D path).val * poincareProduct D p path := by
  induction path with
  | nil => simp [Chain.denominator,meetWeight,poincareProduct]
  | snoc path T ih =>
      simp only [Chain.denominator,meetWeight,poincareProduct,map_mul,ih,
        scalar_specialize,zpow_add,Units.val_mul]
      ring

theorem denominator_specialize_ne_zero (p : ℕ) (hp : p.Prime)
    {I J : Index n} (path : Chain I J) :
    specialize p hp (Chain.denominator D path) ≠ 0 := by
  rw [denominator_specialize]
  exact mul_ne_zero (Units.ne_zero _) (poincareProduct_ne_zero D p hp path)

/-- The boundary case has no facet factor to cancel. -/
example (p : ℕ) (I : Index n) :
    meetWeight D (.nil I) = 0 ∧ poincareProduct D p (.nil I) = 1 := by
  simp only [meetWeight,poincareProduct,and_self]

/-- A single step has exactly the common-facet Poincare factor. -/
example (p : ℕ) (I J : Index n) :
    poincareProduct D p (.snoc (.nil I) J) = PoincareValue D p (meet I J) := by
  simp only [poincareProduct,one_mul]

variable (K : KLRealization c) (L : Laws K D)

/-- Coordinatewise specialization of the actual cleared chain identity. -/
theorem cleared_specialize (p : ℕ) (hp : p.Prime) {I J : Index n}
    (path : Chain I J) (w : AffinePermutation n) :
    specialize p hp (Chain.denominator D path) *
        specialize p hp (K.standard.repr (Chain.raw K D L path) w) =
      specialize p hp (K.standard.repr (Chain.numerator K D path) w) := by
  have h := congrArg (fun x : Hecke.Algebra n => K.standard.repr x w)
    (Chain.cleared K D L path)
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul] at h
  simpa only [map_mul] using congrArg (specialize p hp) h

/-- Cancellation once full-flag convolution and the actual gallery-lift
count have been supplied. No count is defined by either equality. -/
theorem normalized_raw_of_fullGallery_count
    {k : Type} [Field k] [NeZero n]
    (p : ℕ) (hp : p.Prime) {I J : Index n} (path : Chain I J)
    (source target : PolynomialFullGallery.FullFlag k n) (w : AffinePermutation n)
    (hnum : specialize p hp (K.standard.repr (Chain.numerator K D path) w) =
      ((primeUnit p hp) ^ (vertexWeight D path - c.system.length w)).val *
        (Nat.card (PolynomialFullGallery.FullGallery path source target) : ℚ))
    (hcount : (Nat.card (PolynomialFullGallery.FullGallery path source target) : ℚ) =
      poincareProduct D p path *
        (Nat.card (PolynomialFlags.Gallery path
          (PolynomialFullGallery.forget I source) (PolynomialFullGallery.forget J target)) : ℚ)) :
    specialize p hp (K.standard.repr (Chain.raw K D L path) w) =
      ((primeUnit p hp) ^ (Chain.weight D path - c.system.length w)).val *
        (Nat.card (PolynomialFlags.Gallery path
          (PolynomialFullGallery.forget I source) (PolynomialFullGallery.forget J target)) : ℚ) := by
  have hc := cleared_specialize D K L p hp path w
  rw [denominator_specialize,hnum,hcount] at hc
  have he : ((primeUnit p hp) ^ (vertexWeight D path - c.system.length w)).val =
      ((primeUnit p hp) ^ meetWeight D path).val *
        ((primeUnit p hp) ^ (Chain.weight D path - c.system.length w)).val := by
    rw [←Units.val_mul,←zpow_add,weight_eq]
    congr 2
    ring
  rw [he] at hc
  apply mul_left_cancel₀
    (mul_ne_zero (Units.ne_zero _) (poincareProduct_ne_zero D p hp path))
  calc
    (((primeUnit p hp) ^ meetWeight D path).val * poincareProduct D p path) *
        specialize p hp (K.standard.repr (Chain.raw K D L path) w) = _ := hc
    _ = _ := by ring

#print axioms scalar_specialize
#print axioms denominator_specialize
#print axioms normalized_raw_of_fullGallery_count
end Guralnick.PolynomialConvolutionNormalization
