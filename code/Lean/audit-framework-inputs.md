# Field-level ledger: affine and Schur framework

Reviewed 2 November 2026 against the updated `../main.tex`. This supplements
`literature-inputs.md`; `audit-updated-transfer.md` covers the representation
fields. These are explicit parameters, not declared Lean axioms. The
comparison retains the source-audit qualifications in
`audit-primary-affine.md`; it does not assert a new formal proof of a
source theorem.

All Lean names below have prefix `Guralnick`. The executable statements
are in `Hecke.lean`, `CanonicalRefinement.lean` and
`FullFlagHeckeConvolution.lean`. Exact structure declarations are reproduced
at the end for inspection; imported definitions, rather than English
summaries, determine their meaning.

## Coxeter fields

| Field | Source and translation to the paper |
|---|---|
| `WindowCoxeter.system` | Affine type-A Coxeter realization of the actual balanced periodic-permutation group. Björner–Brenti, *Affine Permutations of Type A*, §3, Propositions 3.1–3.3; the paper cites their later book *Combinatorics of Coxeter Groups*. The formal group is not a collection of freely assigned window labels. |
| `WindowCoxeter.simple_window` | Same realization: finite adjacent transpositions and the affine seam transposition. `Fin n` has zero-based slots; entries are one-based window values. `s=0` exchanges positions 0 and 1 periodically, giving `[0,2,...,n-1,n+1]`. |
| `WindowCoxeter.length_formula` | Same source's inversion formula. The sum of absolute floor differences is computed on the actual window. The family's length gap and adjacent-entry descent tests are derived, not fields. |

The field `Hecke.Theory.coxeter` supplies these three data; `.kl` and
`.positivity` supply the next two structures. `TheoryFamily` requests
them only at `n=2*m+1`, `m≥2`; no assertion at invalid small affine ranks
is needed by the endpoint.

## Ordinary KL fields

These fields collectively state the usual ordinary Hecke/KL basis and bar
framework of Kazhdan–Lusztig (1979), §1. The actual algebra is defined
first by generators and the quadratic/braid relations. The parameter
conversion is `H_s=v*T_s`, `Q=v⁻²`; consequently `C_s=H_s+v` and proper
canonical coordinates have strictly positive `v`-degree. This is the
paper's `def:affine-hecke-conventions` and `def:hecke-kl-basis`.

| Field | Exact mathematical role |
|---|---|
| `KLRealization.standard` | Standard basis of the presented algebra indexed by actual affine permutations. |
| `.standard_reduced` | Identifies that basis with products of the actual generators along every reduced word. |
| `.bar` | Ring automorphism implementing the bar; semilinearity is stated in the next field. |
| `.bar_scalar` | Inverts Laurent scalars (`v↦v⁻¹`). |
| `.bar_generator` | Sends `H_s` to `H_s+v−v⁻¹`, its inverse by the quadratic relation. |
| `.canonical` | Canonical basis of the same algebra. |
| `.bar_canonical` | Each canonical vector is bar fixed. |
| `.canonical_diagonal` | Its coefficient at its own standard index is one. |
| `.canonical_lower` | Every different standard coordinate lies in `v ℤ[v]`. This includes zero coordinates. |
| `.canonical_support` | Nonzero coordinates have the subword-defined Bruhat relation. |
| `.polynomial` | Ordinary polynomial in `ℤ[Q]` for each pair. Its value is constrained by the next field; no family polynomial is assigned. |
| `.polynomial_normalization` | `h_{y,w}(v)=v^(length(w)−length(y))*P_{y,w}(v⁻²)`. `normalize` is an injective exponent substitution, proved in `FidelityKL.normalize_injective`. |

The project derives bar involutivity, uniqueness of these realizations,
KL inversion and diagram invariance. It does not construct the bases or
prove their existence. Ordinary positivity is supplied separately:

| Field | Precise source and scope |
|---|---|
| `PositivityInput.standard_nonnegative` | Elias–Williamson, *The Hodge theory of Soergel bimodules*, Corollary 1.2(1). Every ordinary canonical-to-standard Laurent coefficient is nonnegative. |
| `.product_nonnegative` | Same source, Corollary 1.2(2). Every canonical multiplication coefficient is nonnegative. |

The paper also cites KL80/Springer82 for its affine geometric positivity
route, and cites Elias–Williamson in the positivity argument itself.
The formal interface explicitly names the latter. It does not assume
positivity after dividing the main web by its parabolic denominator;
the paper's argument on the undivided product is proved separately.

## Canonical refinement field

| Field | Source, hypotheses and translation |
|---|---|
| `StandardCompatibility.canonical_span` | Williamson, corrected *Singular Soergel bimodules*, §2.3, (2.3.1), for arbitrary finitary parabolics; Cui, Lemma 3.1, Theorem 3.1 and (3.4)–(3.5), for the affine Schur basis dictionary. The element has all prescribed left and right descents (`DoubleMaximal`), so its canonical vector lies in the span of normalized double-coset standard sums (`SchurCorner`). Both parabolics are finite by the proved longest-element construction. |

This is the sole field inside `PolynomialWebLiterature.refinement`.
Williamson's normalization uses `v` as here; Cui's parameter is replaced
by `v⁻¹`. The paper's `theta_A(C_gamma)=C_(w_A^+)` has leading coefficient
one. Partition of standard double cosets, the coordinate ratio under
refinement, and the reduction of canonical support to this one field are
proved in Lean. The field itself remains cited input, consistent with
`lem:affine-schur-dictionary` and `lem:output-refinement`.

## Full-flag fields

| Field | Source, hypotheses and translation |
|---|---|
| `FullFlagHeckeConvolution.Input.orbits` | Lusztig, *Aperiodicity in quantum affine gl_n*, §§1.3–1.5, especially Lemma 1.5: classification of pairs of full periodic polynomial-lattice flags. Lean restricts to the balanced component and therefore uses the sum-zero affine group, not all extended affine degrees. `RelativePosition` is an actual simultaneous Laurent-linear change of coordinates on the two flags. |
| `.convolution` | Lusztig §§1.7–1.9 and Cui §7.1, Lemma 7.1: binary convolution realizes Hecke multiplication on full flags. `value` uses the standard Hecke coordinate times `v^length(w)`, turning `H_w=v^length(w) T_w` into the orbit-characteristic normalization. The target is the left kernel argument and the source the right, so `(x*y)(target,source)` sums `x(target,middle)*y(middle,source)`. |

`PolynomialWebLiterature.full_flag` supplies those two fields for each
prime `p`, over `GaloisField p 2`. This is a deliberate counting
specialization: `Q=p²`, `v=1/p` allows rational specialization at infinitely
many values. This `p` is a dummy counting prime, unrelated to the
representation-theoretic characteristic bound. The paper counts over all
prime powers; using the infinite subset of prime squares suffices for its
polynomial identity.

The input does not state any six-map count, partial-flag formula, arbitrary
chain convolution, Poincaré cancellation, original canonical correction or
row sum. Those are derived. Completion from polynomial Laurent lattices
to the paper's power-series lattices and preservation of all relevant
quotients are also proved, as detailed in `audit-model-comparisons.md`.

## Web-category boundary

The paper's global category isomorphism `lem:web-realization` cites
Shen–Song–Wang, Theorem 4.16 and Proposition 4.18(1). Its local annular
presentation also cites Lacabanne–Tubbenhauer–Vaz and the symmetric-web
presentation literature. These explanatory equivalences are not additional
fields in the final theorem. The formal proof defines the algebraic
split/merge maps directly and proves that the chosen labeled graph
presentation evaluates to them. Global category equivalence and arbitrary
isotopy invariance remain outside the verification. Thus this ledger does
not misidentify a fixed-graph equality as a theorem about every annular web.

## Literal executable structures

The following extracts are copied from the current source. Surrounding
variables are `c : WindowCoxeter n`, `K : KLRealization c`,
`D : ∀ I : ParabolicWeb.Index n, ParabolicWeb.LongestData c I`, and,
for full flags, `p : ℕ`, `[Fact p.Prime]`, `hp : p.Prime`, `[NeZero n]`.


From `Guralnick/Hecke.lean`:

```lean
structure WindowCoxeter (n : ℕ) where
  system : CoxeterSystem (AffineCoxeter.matrix n) (AffinePermutation n)
  simple_window : ∀ s i, (system.simple s).entry i = simpleEntry s i
  length_formula : ∀ w, system.length w = w.inversionCount
```

From `Guralnick/Hecke.lean`:

```lean
structure KLRealization {n : ℕ} (c : WindowCoxeter n) where
  standard : Basis (AffinePermutation n) R (Algebra n)
  standard_reduced : ∀ l : List (Fin n), c.system.IsReduced l →
    standard (c.system.wordProd l) = word l
  bar : Algebra n ≃+* Algebra n
  bar_scalar : ∀ r : R, bar (algebraMap R (Algebra n) r) =
    algebraMap R (Algebra n) (LaurentPolynomial.invert r)
  bar_generator : ∀ i : Fin n, bar (H i) = H i +
    algebraMap R (Algebra n) (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1))
  canonical : Basis (AffinePermutation n) R (Algebra n)
  bar_canonical : ∀ w, bar (canonical w) = canonical w
  canonical_diagonal : ∀ w, standard.repr (canonical w) w = 1
  canonical_lower : ∀ y w, y ≠ w →
    Positivity.LowerBound (standard.repr (canonical w) y) 1
  canonical_support : ∀ y w, standard.repr (canonical w) y ≠ 0 → Bruhat c y w
  polynomial : AffinePermutation n → AffinePermutation n → Polynomial ℤ
  polynomial_normalization : ∀ y w,
    standard.repr (canonical w) y =
      normalize ((c.system.length w : ℤ) - c.system.length y) (polynomial y w)
```

From `Guralnick/Hecke.lean`:

```lean
structure PositivityInput {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c) : Prop where
  standard_nonnegative : ∀ y w, Positivity.Nonnegative (K.standard.repr (K.canonical w) y)
  product_nonnegative : ∀ x y z,
    Positivity.Nonnegative (K.canonical.repr (K.canonical x * K.canonical y) z)
```

From `Guralnick/CanonicalRefinement.lean`:

```lean
structure StandardCompatibility : Prop where
  canonical_span : ∀ (I J : Index n) (w : AffinePermutation n),
    letI : Finite (subgroup c I) := (D I).finite
    letI : Finite (subgroup c J) := (D J).finite
    DoubleMaximal c I J w →
      K.canonical w ∈ SchurCorner K (subgroup c I) (subgroup c J)
```

From `Guralnick/PolynomialWebLiterature.lean`:

```lean
structure PolynomialWebLiterature {n : ℕ} [NeZero n] (T : Hecke.Theory n) where
  refinement : CanonicalRefinement.StandardCompatibility T.kl (polynomialLongest T)
  full_flag : ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    FullFlagHeckeConvolution.Input T.kl p hp
```

From `Guralnick/FullFlagHeckeConvolution.lean`:

```lean
structure Input : Prop where
  orbits : OrbitClassification (GaloisField p 2) n
  convolution : ∀ (x y : Hecke.Algebra n) (target source : FullFlag (GaloisField p 2) n),
    value K p hp orbits (x*y) target source =
      ∑ᶠ middle : FullFlag (GaloisField p 2) n,
        value K p hp orbits x target middle * value K p hp orbits y middle source
```
