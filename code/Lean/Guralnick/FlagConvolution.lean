import Guralnick.FlagGallery
import Guralnick.CanonicalChains
import Guralnick.AffineLatticePosition
import Guralnick.PolynomialsFromCounts
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The general affine-flag convolution input

All objects in this interface have independent definitions: actual Laurent
lattices, affine-window coordinate changes, integral inclusion/merge maps,
and the intermediate flags of an arbitrary finite chain. The external
statement is the general normalized flag-convolution realization (BLM and
Lusztig's periodic-lattice model, with the Hecke normalization of Cui/SSW).
It contains no family-specific count, support or correction formula.

Cui §7.1 (including Lemma 7.1) gives the polynomial periodic convolution
model. `PolynomialFlagConvolution.Input.toCompleted` now derives this
completed-model interface from that independently defined source model:
completion, degree, arbitrary cyclic masks, and galleries are compared by
proved maps. Finiteness of fixed-endpoint galleries is proved separately.
The general normalized polynomial convolution theorem remains an external
framework input. Its arbitrary-mask formulation includes the usual finite
parabolic refinement normalization and is not literally a single theorem
stated in Cui §7.1.

We use fields of cardinality p² and specialize v to 1/p. This is sufficient
to recover Laurent identities by the proved interpolation theorem.
-/

noncomputable section
namespace Guralnick.FlagConvolution
open Hecke ParabolicWeb CanonicalChains LatticeFlags
open PolynomialsFromCounts

variable {n : ℕ} (k : Type) [Field k]

variable {k} {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)

/-- The completed-model interface supplied by the proved polynomial-model
conversion. Relative position is specified
by one actual Laurent-linear coordinate change and the actual affine window.
The exponent is calculated from the chain's parabolic longest elements.
All claims range over arbitrary chains and affine indices. -/
structure Input : Prop where
  realization : ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (I J : Index n) (w : AffinePermutation n),
      ∃ (source : Flag (GaloisField p 2) n (retained I))
        (target : Flag (GaloisField p 2) n (retained J)),
        AffineLatticePosition.RelativePosition (GaloisField p 2) n target source w
  specialization : ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ {I J : Index n} (path : Chain I J)
      (source : Flag (GaloisField p 2) n (retained I))
      (target : Flag (GaloisField p 2) n (retained J)) (w : AffinePermutation n),
      AffineLatticePosition.RelativePosition (GaloisField p 2) n target source w →
      specialize p hp (K.standard.repr (Chain.raw K D L path) w) =
        ((primeUnit p hp) ^ (Chain.weight D path - c.system.length w)).val *
          (Nat.card (Gallery (GaloisField p 2) path source target) : ℚ)

/-- A nonzero standard coordinate has a genuine nonempty gallery over
some finite field. Thus support can be investigated using actual flags;
the existence of critical states is not assumed from the coefficient. -/
theorem nonempty_gallery_of_nonzero (C : Input K D L) {I J : Index n}
    (path : Chain I J) (w : AffinePermutation n)
    (hne : K.standard.repr (Chain.raw K D L path) w ≠ 0) :
    ∃ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∃ (source : Flag (GaloisField p 2) n (retained I))
        (target : Flag (GaloisField p 2) n (retained J)),
        AffineLatticePosition.RelativePosition (GaloisField p 2) n target source w ∧
        Nonempty (Gallery (GaloisField p 2) path source target) := by
  have hex : ∃ (p : ℕ) (hp : p.Prime),
      specialize p hp (K.standard.repr (Chain.raw K D L path) w) ≠ 0 := by
    by_contra h
    apply hne
    apply zero_of_prime_specializations
    intro p hp
    by_contra hn
    exact h ⟨p, hp, hn⟩
  obtain ⟨p, hp, hspec⟩ := hex
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨source, target, hpos⟩ := C.realization p hp I J w
  refine ⟨p, hp, source, target, hpos, ?_⟩
  apply (Nat.card_ne_zero.mp ?_).1
  intro hz
  apply hspec
  rw [C.specialization p hp path source target w hpos, hz, Nat.cast_zero, mul_zero]

/-- Once an ORIGINAL gallery count is proved, the actual standard
coefficient follows from generic convolution and proved interpolation. -/
theorem coordinate_of_counts (C : Input K D L) {I J : Index n}
    (path : Chain I J) (w : AffinePermutation n) (P : Polynomial ℤ)
    (hcount : ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∃ (source : Flag (GaloisField p 2) n (retained I))
        (target : Flag (GaloisField p 2) n (retained J)),
        AffineLatticePosition.RelativePosition (GaloisField p 2) n target source w ∧
        (Nat.card (Gallery (GaloisField p 2) path source target) : ℚ) =
          Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2) P) :
    K.standard.repr (Chain.raw K D L path) w =
      normalize (Chain.weight D path - c.system.length w) P := by
  apply normalized_of_count_specializations
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨source, target, hpos, hc⟩ := hcount p hp
  rw [C.specialization p hp path source target w hpos, hc]

/-- For example, showing the count at every endpoint pair of the specified
relative position is sufficient; orbit realization supplies a pair. -/
theorem coordinate_of_uniform_count (C : Input K D L) {I J : Index n}
    (path : Chain I J) (w : AffinePermutation n) (P : Polynomial ℤ)
    (hcount : ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (source : Flag (GaloisField p 2) n (retained I))
        (target : Flag (GaloisField p 2) n (retained J)),
        AffineLatticePosition.RelativePosition (GaloisField p 2) n target source w →
        (Nat.card (Gallery (GaloisField p 2) path source target) : ℚ) =
          Polynomial.eval₂ (Int.castRingHom ℚ) ((p : ℚ)^2) P) :
    K.standard.repr (Chain.raw K D L path) w =
      normalize (Chain.weight D path - c.system.length w) P := by
  apply coordinate_of_counts K D L C
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨source, target, hpos⟩ := C.realization p hp I J w
  exact ⟨source, target, hpos, hcount p hp source target hpos⟩

end Guralnick.FlagConvolution
