import Guralnick.KLFamily
import Guralnick.RationalCohomology
import Guralnick.SLQuotient
import Guralnick.AbsoluteIrreducibility
import Guralnick.FamilyNontriviality

/-!
# The named module family and the precise literature transfer

The external statements below are universal statements about actual
highest-weight modules and actual regular and finite-group first cohomology.
They do not assert the manuscript's family transfer or its
row sum. We construct the family's modules and prove their transfer from
these inputs, using the formalized weights, KL indices and central descent.

`AndersenAJS` combines AJS's rank-dependent eventual character-formula
theorem with Andersen's degree-one formula and the general spherical
dictionary, in Lübeck's Theorems 3.1 and 4.5 conventions. `BNP` is the
`s=1,r=1,nu=0` specialization of BNP Theorem 7.5, for arbitrary restricted
principal-block highest weights. The regular-cochain interpretation is
Jantzen I (1985 preprint), Proposition 4.16. All remain explicit arguments.
-/

noncomputable section
namespace Guralnick.LiteratureTransfer
open HighestWeight

/-- An actual simple rational highest-weight module. The matrix/torus and
polynomial predicates have independent definitions, unrelated to KL values. -/
structure SimpleModule (k : Type) [Field k] (n : ℕ) (wt : Weights.RootLattice n) where
  rep : Rep k (SL n k)
  highest : SimpleHighestWeight rep wt.val
  polynomial : RationalCohomology.IsPolynomialRepresentation rep

def finiteLeftMinimal {n : ℕ} (c : Hecke.WindowCoxeter n) (b : AffinePermutation n) : Prop :=
  ∀ a q : Fin n, a.val + 1 = q.val → ¬c.system.IsLeftDescent b q

def primeEmbedding (n p : ℕ) [Fact p.Prime] :
    SL n (ZMod p) →* SL n (Cohomology.PrimeClosure p) :=
  Matrix.SpecialLinearGroup.map (algebraMap (ZMod p) (Cohomology.PrimeClosure p))

/-- The existence/classification theorem is required for every restricted
dominant root-lattice weight, not just the proposed family. -/
def HighestWeightExistence : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ wt : Weights.RootLattice (2 * m + 1),
      DominantRestricted (p : ℤ) wt.val →
      Nonempty (SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)

/-- AJS + Andersen + the general ordinary/spherical normalization, for all
dominant restricted principal-block labels and all their simple modules.
The ordinary lower endpoint is explicitly w0. -/
def AndersenAJS (T : Hecke.TheoryFamily) : Prop :=
  ∀ (m : ℕ) (hm : 2 ≤ m), ∃ p₀ : ℕ,
    ∀ (p : ℕ) (hp : p.Prime), p₀ ≤ p → 2 * m + 1 < p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (wt : Weights.RootLattice (2 * m + 1))
        (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)
        (b : AffinePermutation (2 * m + 1)),
        finiteLeftMinimal (T m hm).coxeter b →
        DominantRestricted (p : ℤ) wt.val →
        wt.val = b.dotZero (p : ℤ) (Weights.rho m) →
        (Module.finrank (Cohomology.PrimeClosure p) (RationalCohomology.RationalH1 A.rep) : ℤ) =
          ((T m hm).kl.standard.repr ((T m hm).kl.canonical
            (AffinePermutation.longest (2 * m + 1) * b))
            (AffinePermutation.longest (2 * m + 1))) 1

/-- BNP's prime-field specialization gives a vector-space isomorphism, with
its full restricted principal-block condition. The cited theorem states an
isomorphism, not that a specified cocycle restriction is the isomorphism. -/
def BNP : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime), 5 * (2 * m) ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (wt : Weights.RootLattice (2 * m + 1))
      (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)
      (b : AffinePermutation (2 * m + 1)),
      DominantRestricted (p : ℤ) wt.val →
      wt.val = b.dotZero (p : ℤ) (Weights.rho m) →
      Nonempty (RationalCohomology.RationalH1 A.rep ≃ₗ[Cohomology.PrimeClosure p]
        Cohomology.H1 (restrictPrime (2 * m + 1) p A.rep))

/-- Steinberg restricted irreducibility. Nontriviality of the actual family
is proved directly from a finite torus element in `FamilyNontriviality`. -/
def Steinberg : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (wt : Weights.RootLattice (2 * m + 1))
      (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt),
      DominantRestricted (p : ℤ) wt.val →
      Cohomology.Irreducible (restrictPrime (2 * m + 1) p A.rep)

/-- General finite-group simplicity in the range avoiding all small exceptions. -/
def PSLSimplicity : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime), 5 * (2 * m) ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    IsSimpleGroup (Cohomology.PSL m p)

structure Inputs (T : Hecke.TheoryFamily) : Prop where
  existence : HighestWeightExistence
  andersen : AndersenAJS T
  bnp : BNP
  steinberg : Steinberg
  simple : PSLSimplicity

variable {T : Hecke.TheoryFamily} (I : Inputs T)

/-- The manuscript's algebraic module is chosen by its actual highest weight. -/
def familyAlgebraic {m j p : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    [Fact p.Prime] (hp : 2 * m + 1 < p) :
    SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) (Weights.familyWeight m j p) :=
  Classical.choice (I.existence m hm p Fact.out (Weights.familyWeight m j p)
    (Weights.familyWeight_dominantRestricted hm hj hjm hp))

/-- The actual named PSL module: finite restriction followed by central descent. -/
def familyModule {m j p : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    [Fact p.Prime] (hp : 2 * m + 1 < p) :
    Rep (Cohomology.PrimeClosure p) (Cohomology.PSL m p) :=
  let A := familyAlgebraic I hm hj hjm hp
  SLQuotient.descended (2 * m + 1) p (by omega) (Weights.familyWeight m j p)
    A.rep A.highest.2.1 A.highest.2.2

theorem familyModule_admissible {m j p : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    [Fact p.Prime] (hp : 2 * m + 1 < p) (hBNP : 5 * (2 * m) ≤ p) :
    Cohomology.Admissible (familyModule I hm hj hjm hp) := by
  let A := familyAlgebraic I hm hj hjm hp
  letI := I.simple m hm p Fact.out hBNP
  have hs := I.steinberg m hm p Fact.out (Weights.familyWeight m j p) A
    (Weights.familyWeight_dominantRestricted hm hj hjm hp)
  exact SLQuotient.descended_admissible (2 * m + 1) p (by omega)
    (Weights.familyWeight m j p) A.rep A.highest hs
      (HighestWeight.family_restrictPrime_nontrivial hm hj hjm hp A.rep A.highest.2.2)

/-- The exact inverse-dot equality needed by both external transfer theorems. -/
theorem family_dot_label {m j p : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (Weights.familyWeight m j p).val =
      (Family.affine hm hj hjm)⁻¹.dotZero (p : ℤ) (Weights.rho m) := by
  exact (Family.inverse_dotZero_eq_coordinate hm hj hjm).symm

/-- The rank-dependent eventual character-formula threshold, supplied by
AJS through the general Andersen input. The BNP bound is imposed separately. -/
def threshold (I : Inputs T) (m : ℕ) (hm : 2 ≤ m) : ℕ :=
  Classical.choose (I.andersen m hm)

/-- The full application equality for the manuscript's named module. Its
right-hand side is the actual fixed-source ordinary KL coefficient. -/
theorem familyModule_h1_dimension {m j p : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    [Fact p.Prime] (hp : 2 * m + 1 < p) (hp₀ : threshold I m hm ≤ p)
    (hBNP : 5 * (2 * m) ≤ p) :
    Cohomology.h1Dimension (familyModule I hm hj hjm hp) = Hecke.coefficients T m j := by
  let A := familyAlgebraic I hm hj hjm hp
  let b := (Family.affine hm hj hjm)⁻¹
  have hdom := Weights.familyWeight_dominantRestricted hm hj hjm hp
  have hlabel := family_dot_label (p := p) hm hj hjm
  have hmin : finiteLeftMinimal (T m hm).coxeter b := by
    intro a q haq
    exact Hecke.inverse_family_no_finite_left_descent hm hj hjm (T m hm).coxeter a q haq
  have hRat := Classical.choose_spec (I.andersen m hm) p Fact.out hp₀ hp
    (Weights.familyWeight m j p) A b hmin hdom hlabel
  let e := Classical.choice (I.bnp m hm p Fact.out hBNP (Weights.familyWeight m j p)
    A b hdom hlabel)
  have hdim : Cohomology.h1Dimension (familyModule I hm hj hjm hp) =
      Module.finrank (Cohomology.PrimeClosure p) (RationalCohomology.RationalH1 A.rep) := by
    calc
      _ = Cohomology.h1Dimension (restrictPrime (2 * m + 1) p A.rep) :=
        SLQuotient.descended_h1_dimension (2 * m + 1) p (by omega)
          (Weights.familyWeight m j p) A.rep A.highest.2.1 A.highest.2.2
      _ = _ := e.finrank_eq.symm
  apply Int.ofNat.inj
  change (Cohomology.h1Dimension (familyModule I hm hj hjm hp) : ℤ) =
    (Hecke.coefficients T m j : ℤ)
  rw [hdim, hRat]
  exact (Hecke.coefficients_inverse_canonical T hm hj hjm).symm

theorem familyModule_absolutelyAdmissible {m j p : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) [Fact p.Prime]
    (hp : 2 * m + 1 < p) (hBNP : 5 * (2 * m) ≤ p) :
    Cohomology.AbsolutelyAdmissible (familyModule I hm hj hjm hp) :=
  Cohomology.admissible_absolutelyAdmissible _ (familyModule_admissible I hm hj hjm hp hBNP)

/-- Every substantive input to the old broad transfer interface is now
derived for the actual KL coefficients and the named module family, from
the precise general literature inputs above. No row sum is used here. -/
theorem primeFieldTransfer (I : Inputs T) :
    Cohomology.PrimeFieldTransfer (Hecke.coefficients T) := by
  intro m hm
  obtain ⟨p₀, hAnd⟩ := I.andersen m hm
  refine ⟨p₀, ?_⟩
  intro p hp hp₀ hBNP
  letI : Fact p.Prime := ⟨hp⟩
  have hpN : 2 * m + 1 < p := by omega
  let modules (j : Fin m) := familyModule I hm (show 1 ≤ j.val + 1 by omega)
    (show j.val + 1 ≤ m from by omega) hpN
  refine ⟨modules, ?_, ?_, ?_⟩
  · intro j
    exact familyModule_admissible I hm (by omega) (by omega) hpN hBNP
  · intro j
    have hA := familyModule_admissible I hm (show 1 ≤ j.val + 1 by omega)
      (show j.val + 1 ≤ m from by omega) hpN hBNP
    letI : FiniteDimensional (Cohomology.PrimeClosure p) (modules j) := hA.1
    exact Cohomology.finiteDimensional_H1 (modules j)
  · intro j
    have hj : 1 ≤ j.val + 1 := by omega
    have hjm : j.val + 1 ≤ m := by omega
    let A := familyAlgebraic I hm hj hjm hpN
    let b := (Family.affine hm hj hjm)⁻¹
    have hdom := Weights.familyWeight_dominantRestricted hm hj hjm hpN
    have hlabel := family_dot_label (p := p) hm hj hjm
    have hmin : finiteLeftMinimal (T m hm).coxeter b := by
      intro a q haq
      exact Hecke.inverse_family_no_finite_left_descent hm hj hjm (T m hm).coxeter a q haq
    have hRat := hAnd p hp hp₀ hpN (Weights.familyWeight m (j.val + 1) p) A b hmin hdom hlabel
    let e := Classical.choice
      (I.bnp m hm p hp hBNP (Weights.familyWeight m (j.val + 1) p) A b hdom hlabel)
    have hdim : Cohomology.h1Dimension (modules j) =
        Module.finrank (Cohomology.PrimeClosure p) (RationalCohomology.RationalH1 A.rep) := by
      calc
        _ = Cohomology.h1Dimension (restrictPrime (2 * m + 1) p A.rep) :=
          SLQuotient.descended_h1_dimension (2 * m + 1) p (by omega)
            (Weights.familyWeight m (j.val + 1) p) A.rep A.highest.2.1 A.highest.2.2
        _ = _ := e.finrank_eq.symm
    apply Int.ofNat.inj
    change (Cohomology.h1Dimension (modules j) : ℤ) =
      (Hecke.coefficients T m (j.val + 1) : ℤ)
    rw [hdim, hRat]
    exact (Hecke.coefficients_inverse_canonical T hm hj hjm).symm

end Guralnick.LiteratureTransfer
