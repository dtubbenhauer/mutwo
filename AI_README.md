# Annular webs and Guralnick's conjecture: AI reading guide

**Tom Goertzen, Abel Lacabanne, Daniel Tubbenhauer and Pedro Vaz**

[Raw guide (current main)](https://raw.githubusercontent.com/dtubbenhauer/mutwo/main/AI_README.md) · [Raw complete text (current main)](https://raw.githubusercontent.com/dtubbenhauer/mutwo/main/ai/paper.md) · [Section files](ai/sections/)

This paper proves that a specified family of ordinary affine Kazhdan--Lusztig mu-coefficients, with fixed lower endpoint the longest finite permutation, has sum `m(m+1)/2`. It identifies these coefficients with first cohomology dimensions of explicit faithful absolutely irreducible modules for `PSL_{2m+1}(F_p)`, for each `m >= 2` and every sufficiently large prime `p`. This disproves Guralnick's absolute boundedness conjecture. The construction uses one fixed annular symmetric web graph; its edge thicknesses vary with `m`.

For a commit-pinned copy, use that same commit in raw URLs in place of `main`; the explicit raw links above follow the current branch. Relative manuscript links on GitHub retain the selected revision.

The mathematical sources are the [manuscript PDF](ai/source.pdf) and [LaTeX source](ai/source.tex). This companion was prepared from the supplied manuscript on **2026-11-03**. The source hashes in [the manifest](ai/manifest.json) identify the exact snapshot. The companion adds navigation and explanations of diagram notation; it does not replace the manuscript or assert additional results.

## Files and reading routes

| File | Contents |
|---|---|
| [Complete reading text](ai/paper.md) | The manuscript in a searchable text format with LaTeX mathematics. |
| [Section files](ai/sections/) | Generated sections for readers with a limited retrieval window. |
| [Diagram source index](ai/diagram-index.md) | Every drawing marker, its invocation and exact source location. |
| [Diagram descriptions](ai/diagrams.md) | The meaning of the web pictures, boundaries, winding and coefficient extraction. |
| [Statement and reference index](ai/index.json) | Structured lookup of statements, labels and bibliography. |
| [Source manifest](ai/manifest.json) | The exact source snapshot and file hashes. |
| [Exact LaTeX source](ai/source.tex) | Original formulas, proofs, cross-references and TikZ definitions. |
| [Exact PDF](ai/source.pdf) | Typeset statements and the original diagrams. |
| [Lean assumptions](code/Lean/ASSUMPTIONS.md) | The formal development's explicit background assumptions. |
| [Lean model comparison](code/Lean/Guralnick/ModelComparisonCounterexample.lean) | A code entry point for examining the cohomological conclusion and its model assumptions. |

Reading the guide alone is enough for orientation; checking a claim requires its statement and proof in the manuscript.

The main conclusion is in Section 6, the affine coefficient theorem in Section 4L, and the dictionary connecting webs to coefficients in Section 2E. Section 5 works out `m=2`. Section 7 describes discovery and AI assistance; it is not needed for the proof. PDF pages and theorem numbers below refer to this snapshot; LaTeX labels provide the more stable identifiers.

## The exact mathematical results

### The affine coefficient identity

Fix integers `m >= 2` and `1 <= j <= m`, and put `N=2m+1`. The affine symmetric group `W=\widetilde S_N` consists of periodic permutations of the integers satisfying

$$
w(i+N)=w(i)+N,\qquad
\sum_{i=1}^{N}w(i)=N(N+1)/2.
$$

Its finite parabolic subgroup is `W_0=S_N`, with longest element `w_0=[N,N-1,...,1]`. Define

$$
\delta_i(j)=\begin{cases}
-1,&i\in\{1,\ldots,j-1,m+2\},\\
1,&i\in\{m,N-j+2,\ldots,N\},\\
0,&\text{otherwise}.
\end{cases}
$$

Empty intervals contribute nothing. The increasing sort of the integers `i+N\delta_i(j)`, for `1<=i<=N`, is the window of `u_{j;m}`. Set `C_{j;m}=u_{j;m}w_0`. Thus its window is the reverse of the increasing window just constructed. The length difference is

$$
D_{j;m}=\ell(C_{j;m})-\ell(w_0)
=2j(N-j)-2(m-j)-3.
$$

For the ordinary affine KL polynomial `P_{x,y}(Q)`, put

$$
\mu_{j;m}=[Q^{(D_{j;m}-1)/2}]P_{w_0,C_{j;m}}(Q).
$$

**Theorem 4L.1** proves

$$
\sum_{j=1}^{m}\mu_{j;m}=\binom{m+1}{2},\qquad
\max_{1\le j\le m}\mu_{j;m}\ge\left\lceil\frac{m+1}{2}\right\rceil.
$$

The statement is a row-sum identity. It does not give a general formula for the individual entries or identify a maximizing `j`. Sources: [endpoint construction](ai/source.tex#L3182), [endpoint lemma](ai/source.tex#L4326), [main theorem](ai/source.tex#L5604), labels `lem:dictionary-endpoints` and `thm:aggregate-web`.

### First cohomology and the quantifiers on the characteristic

Let `k=\overline{\mathbb F}_p`, `G=SL_N(k)` and `H=PSL_N(\mathbb F_p)`. Write `\omega_i` for fundamental weights, `\eta_i=\omega_i+\omega_{N-i}`, `\eta_0=0` and `c=m-j`. The highest weights are

$$
\lambda_{j;m}(p)=(c+2)\eta_{j-1}+(p-c-3)\eta_j+\eta_m.
$$

For `p>N`, Lemma 6A.2 proves that this is `u_{j;m}^{-1}\mathbin{\cdot_p}0`, nonzero, dominant, `p`-restricted, `p`-regular and in the root lattice. The simple rational module `L(\lambda_{j;m}(p))` restricts and descends to the module `M_{j;m}(p)` used below.

The transfer in Section 6B assumes **both** `p>=5(N-1)` **and** Lusztig's character formula for the `p`-restricted weights of `G`. For fixed `N`, all sufficiently large primes satisfy both conditions, by the cited literature. Neither `p>N` nor the displayed numerical comparison bound alone is the full transfer hypothesis.

Under those conditions, Lemmas 6B.1 and 6C.1 give

$$
\dim_k H^1(H,M_{j;m}(p))=\mu_{j;m},
$$

and each `M_{j;m}(p)` is faithful and absolutely irreducible. The root-lattice condition makes the center act trivially; inflation-restriction preserves first cohomology, and simplicity of `H` gives faithfulness for the nontrivial descended module.

**Corollary 6C.2:** for each `m>=2` and every sufficiently large prime `p`,

$$
\sum_{j=1}^{m}\dim_k H^1(H,M_{j;m}(p))=\binom{m+1}{2},
\qquad
\max_j\dim_k H^1(H,M_{j;m}(p))\ge
\left\lceil\frac{m+1}{2}\right\rceil.
$$

The threshold for `p` may depend on `m`. The semisimple rank is `N-1=2m`; both rank and characteristic are allowed to grow. The result does not establish unboundedness at fixed rank or fixed characteristic. Sources: [highest weights](ai/source.tex#L5791), [transfer hypotheses and lemma](ai/source.tex#L5842), [descent and corollary](ai/source.tex#L5890), labels `lem:application-weight`, `prop:application-transfer`, `lem:simple-quotient`, `cor:guralnick`.

## How the proof fits together

The central object is `\mathcal R_m:(N)\to(m,1,m)`. Six split and merge maps follow the boundary sequence

$$
(N)\to(m,1,m)\to(2m,1)\to(1,m-1,1,m-1,1)
\to(1,N-2,1)\to(1,m-1,1,m-1,1)\to(m,1,m).
$$

The `(2m,1)` merge and split pass through the annular cut. Two exposed unit strands bypass the middle merge and split, then rejoin the outer edges. The algebraic expression, in the inverse-permutation convention, is

$$
\mathcal R_m=\frac{M_eC_JC_KC_V}{[m]!^2[m-1]!^4}.
$$

This represents a composite of integral maps. It is bar invariant, but need not be a canonical basis vector. [Construction and normalization](ai/source.tex#L4412), labels `S:MainWeb` and `lem:main-symmetrizer`.

| Step and source | Role in the argument |
|---|---|
| [Proposition 2E.10](ai/source.tex#L4389), p.15; `cor:dictionary-readout` | The coefficient of the normalized standard splitter in a desired canonical vector is `v^{D_{j;m}}P_{w_0,C_{j;m}}(v^{-2})`. Its coefficient of `v` is `\mu_{j;m}`. |
| [Proposition 3C.4](ai/source.tex#L4635), p.18; `prop:gallery-standard` | Counts intermediate flags to compute every standard coefficient of `\mathcal R_m` as a power of `v` times an explicit polynomial built from Gaussian binomial coefficients. |
| [Lemmas 4B.1 and 4C.2](ai/source.tex#L4811), pp.19–21; `lem:undivided-positivity-degree`, `prop:algebraic-six` | Positivity and degree estimates restrict the canonical support to six families. The desired family initially has multiplicities zero or one. |
| [Lemmas 4E.2, 4E.4 and 4F.2](ai/source.tex#L5042), pp.22–25 | Describe the spherical canonical vectors and the four auxiliary families retaining one line or the dual hyperplane condition. Output refinement preserves the relevant vectors. |
| [Lemma 4H.1](ai/source.tex#L5319), pp.25–26; `cor:one-mark-margin` | The four auxiliary families, including their Laurent multiplicities, contribute only in degrees at least three at the distinguished standard coordinate. |
| [Lemma 4I.1](ai/source.tex#L5358), p.26; `lem:all-two-mark-multiplicities` | Comparison of constant coefficients proves that every desired canonical vector occurs exactly once. |
| [Lemmas 4J.1–4K.1](ai/source.tex#L5429), pp.26–28; `lem:Gaussian-truncation`, `lem:Gaussian-cancellation`, `prop:full-correction` | Determine and subtract the spherical correction. The remaining linear coefficient is exactly `\binom{m+1}{2}`. |
| [Theorem 4L.1](ai/source.tex#L5604), p.28 | Reads this linear coefficient as the sum of the desired affine mu-coefficients. |
| [Section 6](ai/source.tex#L5784), pp.31–32 | Transfers those coefficients to first cohomology with the fixed trivial source and descends to the finite simple quotient. |

This table describes the mathematical argument, not a Lean import graph.

## Conventions that affect the result

| Notation or distinction | Meaning here |
|---|---|
| `W`, `\widehat S_N`, `W_0` | Ordinary affine, extended affine and finite symmetric groups respectively. The categorical framework uses the extended algebra; the main calculation has degree zero. |
| `w_0` versus the identity | The fixed lower KL endpoint is `w_0`. This is essential for first cohomology with the trivial module. Arbitrary large extension dimensions do not give that conclusion. |
| Products and diagrams | `(xy)(i)=x(y(i))`. The rightmost factor acts first; strips are read bottom-to-top and annuli inner-to-outer. |
| `v`, `Q`, `q`, `p` | `Q=v^{-2}`; `q` sometimes abbreviates `Q`. Finite-field flag counting produces polynomials in `Q`. The characteristic in the cohomological application is `p`. |
| `[n]` versus `[n]_Q` | `[n]=v^{n-1}+v^{n-3}+...+v^{1-n}`, while `[n]_Q=1+Q+...+Q^{n-1}`. |
| `\theta_A`, `[A]_v`, `C_A`, `\Delta_A` | Canonical and normalized standard Schur vectors, followed by their images under inversion. `C_{j;m}` instead denotes a permutation. |
| Bar versus star | Bar inverts `v` and preserves products. Star sends `H_w` to `H_{w^{-1}}` and reverses products. Winding dots do not simply change sign under bar. |
| Splitter coefficient | Brackets around `B_m` extract its normalized standard coefficient. They do not mean composition, closure or trace. |
| Positivity | The argument applies positivity to the cleared product `d_m\mathcal R_m`, then uses the degree lemma. Positivity of the quotient's canonical multiplicities is not assumed. |
| Thickness and rank | Thick edges represent symmetric powers. `N` is total thickness; the group rank is `N-1`. The gallery parameter `r` counts shifts of each sign. |

The standard splitter satisfies `[B_m]_v=\theta_{B_m}`. A canonical vector requires bar invariance **and** triangularity, with proper standard coefficients in `v\mathbb Z[v]`. The corrected web `\mathcal R_m^{\rm crit}` is still a sum of canonical vectors; the auxiliary vectors remain present, but do not affect its linear coefficient at `B_m`. Sources: [dictionary and conventions](ai/source.tex#L4007), [positivity lemma](ai/source.tex#L4811), [corrected expansion](ai/source.tex#L5613).

## Small examples and the boundary between evidence and theorem

At `m=2`, `N=5`, the increasing windows are

$$
u_{1;2}=[-1,1,3,5,7],\qquad
u_{2;2}=[-4,-1,3,7,10].
$$

The raw standard coefficient of the main web is

$$
[[B_2]_v]\mathcal R_2=v^{-1}+4v+7v^3+7v^5+4v^7+v^9.
$$

Subtracting `(v+v^{-1})B_2` changes the linear coefficient from **4 to 3**, the correct row sum. Section 5 then separates the two desired vectors: `\mu_{1;2}=1` and `\mu_{2;2}=2`, with

$$
P_{w_0,C_{2;2}}(Q)=1+4Q+5Q^2+4Q^3+2Q^4.
$$

The corresponding highest weights have Dynkin coordinates `(p-4,1,1,p-4)` and `(2,p-2,p-2,2)`. [Worked calculation](ai/source.tex#L5656), [cohomological examples](ai/source.tex#L5936).

The introduction reports these exact computations:

| `m` | `N` | Computed row | Row sum |
|---|---|---|---|
| 2 | 5 | `(1,2)` | 3 |
| 3 | 7 | `(1,2,3)` | 6 |
| 4 | 9 | `(1,2,3,4)` | 10 |
| 5 | 11 | `(1,2,3,4,5)` | 15 |

The row-sum theorem holds for all `m>=2`. The individual formula `\mu_{j;m}=j` is explicitly **not proved in general**. Faster growth obtained by enlarging the graph is also speculative. [Computational table and qualification](ai/source.tex#L3238), [final discussion](ai/source.tex#L6294).

## Formalization and cited background

Section 1F and Remark 1F.1 describe a Lean formalization of the explicit affine family, six-map calculation, gallery counts, canonical correction, row-sum identity for every `m>=2`, and deduction of unbounded first cohomology. They also describe formalized `m=2` polynomial identities and a labeled-graph presentation evaluating to the six-map morphism.

The manuscript explicitly says that substantial background is supplied as hypotheses: affine Coxeter and KL theory, positivity, canonical Schur bases, flag-orbit classification and convolution, highest-weight theory, the eventual character formula, the KL-to-cohomology identification, rational-to-finite cohomology comparison and simplicity of the relevant PSL groups. Thus the scope is a formal verification **relative to those stated inputs**, not a claim that all cited mathematics has been formalized. The [manuscript account](ai/source.tex#L3540) and [assumptions file](code/Lean/ASSUMPTIONS.md) are the relevant sources; this reading companion is not an independent audit or rebuild of the Lean development.

Related terminology includes annular webs, affine webs in other sources, symmetric web categories, affine Hecke algebras, affine Schur algebras, canonical bases, Gaussian binomial coefficients, Kazhdan--Lusztig leading coefficients, first extensions and first group cohomology. These terms help locate the paper's connections; the definitions and parameter conventions above fix their use here.
