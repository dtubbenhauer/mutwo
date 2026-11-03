# Annular webs and Guralnick's conjecture — text reading edition

Tom Goertzen, Abel Lacabanne, Daniel Tubbenhauer and Pedro Vaz.

Companion snapshot: 2026-11-03. [Reading guide](../AI_README.md) · [exact TeX](source.tex) · [matching supplied PDF](source.pdf) · [statement and reference index](index.json) · [diagram explanations](diagrams.md).

Using annular webs and Kazhdan--Lusztig mu-coefficients, we disprove Guralnick’s absolute boundedness conjecture for first cohomology.

This is a mechanically generated reading edition of the supplied manuscript, including its proofs and bibliography. Mathematical displays are literal LaTeX code blocks; inline mathematics uses LaTeX. The display fences are intentional: they preserve arrays, normalization and mixed text/diagram formulas without relying on a browser's math renderer. Common mathematical macros are expanded from their definitions. Drawing placeholders D001, D002, ... point to their exact source in the [diagram index](diagram-index.md); they are editorial identifiers, not mathematical variables. The [diagram explanations](diagrams.md) supply the main maps and relations in text. Layout-only material is simplified. The exact source and PDF determine the paper's statements.

The original statement numbers and equation labels are retained. The index records source lines, PDF pages and exact statement/proof source. It records explicit cross-references, not a mechanically verified logical dependency graph. The selected proof route is in the reading guide. See [manifest](manifest.json) for source hashes and conversion checks.

## Contents

- [1. Introduction](#section-1)
- [2. Annular webs and KL coefficients](#section-2)
- [3. The main web](#section-3)
- [4. The base change (main calculation)](#section-4)
- [5. The first example in pictures](#section-5)
- [6. Application to Guralnick's conjecture](#section-6)
- [7. Methods and AI assistance](#section-7)
- [References](#references)

<a id="section-1"></a>

## 1. Introduction

<!-- Source: source.tex lines 2815; PDF page 1. -->


We use webs on an annulus to disprove Guralnick's 1986 conjecture, a classical problem about finite groups, far from the usual home of webs.


<a id="section-1a"></a>

### 1A. The question

<!-- Source: source.tex lines 2820; PDF page 1. -->


How large can the first cohomology of a finite group be? Let $G$ be a finite group, $k$ a field and $M$ a finite-dimensional $kG$-module. The space $H^1(G,M)=\operatorname{Ext}^1_{kG}(k,M)$ classifies extensions $0\to M\to E\to k\to0$, where $k$ is the trivial module. Thus $H^1(G,M)=0$ precisely when every such extension splits. We ask about its dimension when $M$ is as easy as possible: faithful and absolutely irreducible.

<a id="ai-statement-001"></a>


**Remark 1A.1.** [Source](source.tex#L2830); [PDF p. 1](source.pdf#page=1).


First cohomology also has a concrete interpretation in terms of subgroups. Regard $M$ as an additive group and form the semidirect product $M\rtimes G$. Then $H^1(G,M)$ parametrizes the complements to $M$, up to conjugation by elements of $M$. This connects cohomology dimensions with the subgroup structure of finite groups.

In 1986, Guralnick conjectured that there is an absolute constant $C$ such that $\dim_k H^1(G,M)\le C$ for every finite group $G$, every field $k$ and every finite-dimensional faithful absolutely irreducible $kG$-module $M$ [[Gur86](#bib-guralnick), Conjecture~2]; see also [[Lüb20](#bib-luebeck), Conjecture~4.4]. The same constant must work regardless of the group, its rank, the characteristic or the dimension of the module. We call this *Guralnick's conjecture*.

The known dimensions were initially small enough for Guralnick--Hoffman to conjecture $C=2$ [[GH98](#bib-guralnickhoffman), Conjecture~2]. Scott disproved this in 2003 [[Sco03](#bib-scott)], and Bray--Wilson later gave explicit modules with first cohomology of dimension three [[BW08](#bib-braywilson)]. Subsequent computations produced much larger values. Lübeck obtained dimensions $469$ and $36672$ in types $A_7$ and $A_8$, and $3{,}537{,}142$ in type $E_6$, in sufficiently large defining characteristic [[Lüb20](#bib-luebeck), Theorem~4.7]. These calculations suggested rapid growth with the rank, but pushing them further is difficult: even a single relevant KL polynomial can require substantial time and memory [[Lüb20](#bib-luebeck), [SS16](#bib-scottsprowl)].

<a id="ai-statement-002"></a>


**Remark 1A.2.** [Source](source.tex#L2864); [PDF p. 1](source.pdf#page=1).


Large first cohomology dimensions also led to counterexamples to Wall's conjecture on maximal subgroups at the 2012 AIM workshop "Cohomology bounds and growth rates". For the story and its connection with Guralnick's conjecture, see e.g. [[G+12](#bib-aimwall), [B+14](#bib-bendeletalhistory)].

To disprove Guralnick's conjecture, one needs a family whose cohomology dimensions are unbounded. Our explicit family gives such a result:


<a id="cor-intro-guralnick"></a>


**Corollary 1A.3.** (See [Corollary 6C.2](#cor-guralnick)) [Source](source.tex#L2875); [PDF p. 2](source.pdf#page=2).


For each $m\ge2$ and every sufficiently large prime $p$, there is a faithful absolutely irreducible module $M$ for $H=\mathrm{PSL}_{2m+1}(\mathbb F_p)$ over $k=\overline{\mathbb F}_p$ such that 

```latex
\dim_k H^1(H,M)\ge\left\lceil\frac{m+1}{2}\right\rceil.
```

 In particular, Guralnick's absolute boundedness conjecture is false.

The growth is linear in the rank, and the required threshold for $p$ may depend on $m$, so both the rank and the characteristic vary in this construction. The highest weights of the modules are explicit; they are given in [Section 6](#sec-guralnick).

Perhaps more striking is how the counterexamples arise: from the right perspective, the conjecture is "almost obviously false". We use a fixed web (a convenient way of writing a linear map) graph drawn on an annulus, with inputs on the inner boundary and outputs on the outer boundary. The local vertices are splits and merges, but they can meet around the annulus. Crazy enough, in our construction the graph stays the same as $m$ grows; only the edge thicknesses change. And the graph is tiny: its natural toroidal closure (after applying two ordinary merges) has just 14 vertices and 21 edges, exactly like the famous Heawood graph, although the two are not isomorphic, cf. [Figure 1](#fig-toroidal-closure).


<a id="fig-toroidal-closure"></a>


[D001: drawing](diagram-index.md#d001)

**Figure caption.** The toroidal closure of our web graph. Opposite dashed sides are identified. The graph has $14$ vertices, $21$ edges and seven faces of lengths $4,4,5,5,6,6,12$.

Using the canonical expansion of this web, we compute the sum of a family of $m$ affine Kazhdan--Lusztig (KL) $\mu$-coefficients [[KL79](#bib-kl)]. The sum is exactly $m(m+1)/2$, so at least one coefficient is at least $\lceil(m+1)/2\rceil$. This gives the cohomological lower bound. Finally, for the modules considered here, in sufficiently large characteristic, the first cohomology dimension then equals this affine $\mu$-coefficient.

<a id="ai-statement-004"></a>


**Remark 1A.4.** [Source](source.tex#L3061); [PDF p. 2](source.pdf#page=2).


In [[G+26b](#bib-finite)], we also use webs to prove exponential growth for $\mu$-coefficients of finite symmetric groups. The difference essentially is that in [[G+26b](#bib-finite)] we use planar webs, fix the rank and let the web grow, while in this paper we use annular webs, fix the web and let the rank grow. (The idea that "planar = finite" and "annular = affine" has been around for donkey's years in low-dimensional topology; see [[HT27](#bib-ht), Section~1B] for a brief historical overview.)

Note that Scott--Xi [[SX10](#bib-sx)] constructed unbounded affine $\mu$-coefficients in type $A$, and Chen [[Che18](#bib-chen)] treated the other classical affine types. None of [[Che18](#bib-chen), [G+26b](#bib-finite), [SX10](#bib-sx)] can be directly used to refute Guralnick's conjecture.

In other words, we have: 

```latex
\setlength{\fboxsep}{2pt}
\colorbox{blue!6}{
\begin{minipage}{0.85\textwidth}
\centering
\emph{First cohomology dimensions are unbounded, already for
faithful absolutely irreducible modules of finite simple
groups of type A. One annular web graph gives this result.}
\end{minipage}}
```


<a id="section-1b"></a>

### 1B. A recap on annular diagrams

<!-- Source: source.tex lines 3085; PDF page 2. -->


Fix $m\ge2$ and put $N=2m+1$. The affine symmetric group $W=\widetilde S_N$ consists of bijections $w:\mathbb Z\to\mathbb Z$ satisfying $w(i+N)=w(i)+N$ and $\sum_{i=1}^Nw(i)=N(N+1)/2$. We call these annular permutations, and the name is justified momentarily.

The window $[w(1),\ldots,w(N)]$ determines $w$. We compose as functions, $(xy)(i)=x(y(i))$, and write $\ell$ for the Coxeter length. The simple reflection $s_i$ exchanges $i+kN$ and $i+1+kN$ for every $k\in\mathbb Z$, with $i$ read modulo $N$. The finite symmetric group $S_N=\langle s_1,\ldots,s_{N-1}\rangle$ sits inside $W$; its longest element is $w_0=[N,N-1,\ldots,1]$. Right multiplication by $w_0$ therefore reverses the window.

We use the following way to draw elements of $\widetilde S_N$, as well as other objects. A string diagram for $w$ joins $i$ at the bottom to $w(i)$ at the top and repeats with period $N$. Crossings are not vertices: each string continues through them. We draw one period, with its two vertical sides dashed. Identifying these sides at equal heights gives an annulus, with inputs on the inner boundary and outputs on the outer boundary. To draw $xy$, place $x$ above $y$ in the strip. On the annulus, place $x$ outside $y$ and glue the outer boundary of $y$ to the inner boundary of $x$, matching labels and aligning the cuts. In either picture, $y$ acts first. For instance, at $N=5$, 

```latex
\begin{aligned}
s_0&=[0,2,3,4,6],\\
s_1&=[2,1,3,4,5],\\
s_0s_1&=[2,0,3,4,6].
\end{aligned}
\qquad
\text{[D002]}
\quad\longleftrightarrow\quad
\text{[D003]}
```

 [D002](diagram-index.md#d002); [D003](diagram-index.md#d003)

 The gray line becomes the gluing circle, with $s_1$ in the inner band and $s_0$ in the outer band. The boundary labels are residues modulo five: the strings from $2$ and $5$ reach the points labeled $5$ and $1$, representing $0$ and $6$. The winding distinguishes these integers from their residues. Here $\ell(s_0s_1)=2$. The precise conventions are in [Section 2](#sec-dictionary), following [[HT27](#bib-ht), Section~2A].


<a id="section-1c"></a>

### 1C. The main result in more detail

<!-- Source: source.tex lines 3182; PDF page 3. -->


For our main result, we need to construct two annular permutations, the lower and upper endpoint. For first cohomology we need $w_0$ as the lower endpoint, corresponding to the trivial module, see e.g. [[SX10](#bib-sx), Section~4], which is fixed throughout. We construct the upper endpoints by shifting entries of $[1,\ldots,N]$ by one period and sorting. For $1\le j\le m$, set 

```latex
\delta_i(j)=\begin{cases}
-1,&i\in\{1,\ldots,j-1,m+2\},\\
1,&i\in\{m,N-j+2,\ldots,N\},\\
0,&\text{otherwise},
\end{cases}
```

 where empty intervals contribute nothing. Let $u_{j;m}$ have the increasing window obtained by sorting $\{i+N\delta_i(j):1\le i\le N\}$, and put $C_{j;m}=u_{j;m}w_0$. In the strip diagram of $u_{j;m}$, the first $j$ strings cross the left cut and the last $j$ cross the right cut. To draw $C_{j;m}$ on the annulus, place $w_0$ inside $u_{j;m}$. For $m=j=2$, the window construction reads 

```latex
[1,2,3,4,5]
\xrightarrow{\text{shift}}[-4,7,3,-1,10]
\xrightarrow{\text{sort}}[-4,-1,3,7,10]=u_{2;2}.
```

 The two representatives at $m=2$ are drawn in [Figure 2](#fig-intro-example). As we will see below, although these annular permutations look fairly complicated, their annular web pictures are surprisingly easy.

Write $P_{x,y}(Q)$ for the ordinary affine KL polynomial. Set 

```latex
\begin{gather*}
\begin{aligned}
D_{j;m}=\ell(C_{j;m})-\ell(w_0)
=2j(N-j)-2(m-j)-3,\quad
\mu_{j;m}=[Q^{(D_{j;m}-1)/2}]P_{w_0,C_{j;m}}(Q),
\end{aligned}
\end{gather*}
```

 where $[x]$ denotes the coefficient of $x$, and $\mu$ are the $\mu$-coefficients. (For webs we use $Q=v^{-2}$.) Our main calculation gives the sum:


<a id="thm-intro"></a>


**Theorem 1C.1.** (See [Theorem 4L.1](#thm-aggregate-web)) [Source](source.tex#L3223); [PDF p. 3](source.pdf#page=3).


For every $m\ge2$, the family above satisfies 

```latex
\sum_{j=1}^{m}\mu_{j;m}=\frac{m(m+1)}{2}.
```

 In particular, $\lceil(m+1)/2\rceil\leq\max_{1\le j\le m}\mu_{j;m}$.

Our proof computes the row sum without determining its individual terms. [Theorem 1C.1](#thm-intro) then implies [Corollary 1A.3](#cor-intro-guralnick), as explained in [Section 6](#sec-guralnick).

Exact computations give the following for $2\le m\le5$; see [Section 1F](#s-lean) for the code and Lean verification. 

```latex
\begin{array}{c|cccc}
m&2&3&4&5\\\hline
N&5&7&9&11\\
(\mu_{1;m},\ldots,\mu_{m;m})&(1,2)&(1,2,3)&(1,2,3,4)&(1,2,3,4,5)\\
\text{row sum}&3&6&10&15
\end{array}
```

 The theorem proves the row sums for all $m$. (The computed rows suggest $\mu_{j;m}=j$, but we don't know whether this is true for general $m$.) At $m=2$, for instance, $P_{w_0,C_{2;2}}(Q)=1+4Q+5Q^2+4Q^3+2Q^4$. Here $D_{2;2}=9$, so $\mu_{2;2}$ is the coefficient of $Q^4$, namely two. This is the Scott--Xi example [[SX10](#bib-sx), Lemma~3.4], recovered below using webs.


<a id="fig-intro-example"></a>


  ---------------------- ----------------------
   $u_{1;2}=[-1,1,3,5,7]$   $u_{2;2}=[-4,-1,3,7,10]$
   $\text{[D004]}\;\text{[D005]}$ [D004](diagram-index.md#d004); [D005](diagram-index.md#d005)   $\text{[D006]}\;\text{[D007]}$ [D006](diagram-index.md#d006); [D007](diagram-index.md#d007)
  ---------------------- ----------------------

**Figure caption.** The first two representatives, each shown in one period and on the annulus. Composing with $w_0$ at the inner boundary gives the upper endpoints $C_{j;2}$.


<a id="section-1d"></a>

### 1D. The web picture

<!-- Source: source.tex lines 3316; PDF page 4. -->


Recall that a web is a graph with labeled edges and trivalent internal vertices. Its boundary is recorded by the sequence of incident edge labels or thicknesses, say $(a,b,c)$. In a symmetric web, an edge labeled $a$ represents the $a$th symmetric power of the representation carried by a thin label $1$ strand, see e.g. [[RT16](#bib-rosetubbenhauer), [TVW17](#bib-tvw)]. Thickness is conserved at each vertex: a split replaces $(a+b)$ by $(a,b)$, and a merge does the reverse. We use the annular construction of, for example, [[Que15](#bib-queffelec), [LTV23](#bib-ltv)] with symmetric rather than exterior edges, reading from the inner boundary outwards.

Our web $\mathcal R_m:(N)\to(m,1,m)$ is built as follows: Split into $(m,1,m)$ and merge the two $m$-edges across the cut. Expose two more unit strands to obtain $(1,m-1,1,m-1,1)$. Keep the two outer units separate while merging and splitting the middle three edges. Finally, rejoin each retained unit to its neighboring edge. See [Figure 3](#fig-intro-affine-construction) for an illustration.


<a id="fig-intro-affine-construction"></a>


  ---------------------- ------------------------ ------------------------
    \(a\) First split     \(b\) Expose two units   \(c\) Complete the web
   $(2,1,2)$    $(1,1,1,1,1)$     $(2,1,2)$
   $\text{[D008]}$ [D008](diagram-index.md#d008)    $\text{[D009]}$ [D009](diagram-index.md#d009)     $\text{[D010]}$ [D010](diagram-index.md#d010)
   $(3,1,3)$    $(1,2,1,2,1)$     $(3,1,3)$
   $\text{[D011]}$ [D011](diagram-index.md#d011)    $\text{[D012]}$ [D012](diagram-index.md#d012)     $\text{[D013]}$ [D013](diagram-index.md#d013)
  ---------------------- ------------------------ ------------------------

**Figure caption.** Three stages of $\mathcal R_2$ (top) and $\mathcal R_3$ (bottom). The sequences give the output boundaries; the inputs are $(5)$ and $(7)$, respectively. Blue strands have thickness one. The two outer unit strands exposed in (b) are retained through the merge and split.

The displayed intermediate boundaries, together with the blue labels $1$, determine every omitted internal label by conservation at the vertices. For example, at $m=3$ the cyclic merge has thickness $6$ and the middle merge has thickness $5$. As [Figure 4](#fig-intro-annular-family) shows, the graph stays fixed as $m$ grows; only the edge thicknesses change. The six maps are given in [Section 3](#sec-algebraic-gallery).


<a id="fig-intro-annular-family"></a>


$\displaystyle
\mathcal R_m:(N)\longrightarrow(m,1,m),\qquad N=2m+1.$

  ---------------------- ----------------------
         Annulus            Cut-open annulus
   $\vcenter{\hbox{\text{[D014]}}}$ [D014](diagram-index.md#d014)   $\vcenter{\hbox{ 
\text{[D015]}}}$ [D015](diagram-index.md#d015)
  ---------------------- ----------------------

**Figure caption.** The same web $\mathcal R_m$ in two forms. Glue the red dashed sides of the right-hand picture at equal heights to recover the annulus on the left. The blue strands have thickness one.


<a id="section-1e"></a>

### 1E. The proof in a nutshell

<!-- Source: source.tex lines 3391; PDF page 4. -->


The starting point is the relation between canonical bases and KL polynomials. In [[G+26b](#bib-finite)], we used the theorem of Frenkel--Khovanov--Kirillov (FKK) [[FKK98](#bib-fkk)], relating canonical bases in tensor powers to KL polynomials for symmetric groups. Here we need an annular counterpart. We obtain it from the canonical basis of affine Schur theory, using the Hecke realization of annular symmetric webs, see e.g. [[Cui14](#bib-cui), [Lus99](#bib-lusztigaffine), [SSW25](#bib-ssw)]. We explain the comparison and its normalization in [Section 2](#sec-dictionary).

For fixed input and output labels, the relevant web morphism space has a normalized standard basis $[A]_v$ and a canonical basis $\theta_A$. Their indices are affine double cosets determined by the boundary labels. As in KL theory, the canonical basis is characterized by bar invariance and triangularity with respect to the standard basis.

Only one standard coefficient will matter. Let $b_m(f)$ denote the coefficient of $[B_m]_v$ in the standard expansion of $f$, where $B_m:(N)\to(m,1,m)$ is the ordinary split map, called splitter. This splitter is both standard and canonical. Its input packet corresponds to the finite parabolic subgroup $S_N$, and its longest double-coset representative is $w_0$. For the index $A_{j;m}$ corresponding to our upper endpoint $C_{j;m}$, the comparison gives 

```latex
b_m(\theta_{A_{j;m}})
=v^{D_{j;m}}P_{w_0,C_{j;m}}(v^{-2}).
```

 The highest allowed KL degree becomes the coefficient of $v$: thus $[v]\,b_m(\theta_{A_{j;m}})=\mu_{j;m}$. This explains both the choice of the ordinary splitter and the normalization.

Our web $\mathcal R_m$ is bar invariant, but it need not be a canonical element. Lower canonical terms can affect the coefficient we want, just as in [[G+26b](#bib-finite)]. Already at $m=2$, $b_2(\mathcal R_2)=v^{-1}+4v+7v^3+\cdots$. The ordinary splitter occurs with multiplicity $v+v^{-1}$. Subtracting it gives $b_2(\mathcal R_2^{\rm crit})=3v+7v^3+\cdots$. Reading the coefficient before this correction would give four; the desired sum is three.


<a id="fig-intro-critical-correction"></a>


$\displaystyle
\mathcal R_2^{\rm crit}=
\text{[D016]}
\quad-(v+v^{-1})
\text{[D017]}.$ [D016](diagram-index.md#d016); [D017](diagram-index.md#d017)

**Figure caption.** The first correction in $\operatorname{Hom}((5),(2,1,2))$. Subtracting the ordinary splitter leaves the two desired canonical summands and two auxiliary terms, each retaining one line. The auxiliary contributions start in degree three. The individual $\mu$-coefficients are recovered in [Section 5](#sec-aggregate-calibration).

For general $m$, we first compute the standard expansion of $\mathcal R_m$. The split and merge maps describe choices of intermediate flags between fixed input and output flags. Here a flag is a chain of nested subspaces. We fix the input and output flags and count the intermediate choices prescribed by the splits and merges over a finite field $\mathbb F_Q$. For example, an $n$-dimensional space has $\genfrac{[}{]}{0pt}{}{n}{k}_Q$ subspaces of dimension $k$. Requiring a subspace to contain a fixed subspace $U$ amounts to making the corresponding choice in the quotient by $U$. Counting the required lines, hyperplanes and subspaces in this way gives expressions in Gaussian binomial coefficients, also called $q$-binomials. We then substitute $Q=v^{-2}$; the normalization supplies the remaining powers of $v$. These counts are carried out in [Section 3](#sec-algebraic-gallery).

We then determine which canonical elements can occur. If $\mathcal R_m=\sum_A M_A(v)\theta_A$, bar invariance gives $M_A(v)=M_A(v^{-1})$. Together with KL positivity, this turns the degree bounds from the standard calculation into bounds on the multiplicities $M_A$. Only six families survive. One consists of our $m$ elements $\theta_{A_{j;m}}$. Comparing constant coefficients at their standard indices proves that each occurs once.

Four auxiliary families retain one line or impose the dual hyperplane condition. Even after multiplication by their Laurent polynomial multiplicities, their contributions at $B_m$ start in degree three. They therefore do not affect the coefficient of $v$.

The remaining family does affect it. Its webs have one packet of thickness $N$ at both ends, before the ordinary output split. Apart from the initial splitter $B_m$, its canonical elements are differences of consecutive split--merge webs. We determine their multiplicities by successively canceling nonpositive powers in the corresponding standard coefficients; bar symmetry determines the positive powers. Subtracting this family gives 

```latex
\mathcal R_m^{\rm crit}
=\sum_{j=1}^{m}\theta_{A_{j;m}}+E_m,
\qquad b_m(E_m)\in v^3\mathbb Z[v],
```

 where $E_m$ collects the four auxiliary families with a retained line or its dual.

It remains to compute the linear coefficient of the corrected standard expansion. The Gaussian cancellation in [Section 4](#sec-algebraic-relevance) gives 

```latex
\sum_{j=1}^{m}\mu_{j;m}
=[v]\,b_m(\mathcal R_m^{\rm crit})
=[z^{m-1}]\frac{1}{(1-z)^3}
=\binom{m+1}{2}.
```

 The last coefficient counts triples of nonnegative integers summing to $m-1$. Thus the calculation gives the whole row sum without requiring a formula for its individual entries.

<a id="ai-statement-006"></a>


**Remark 1E.1.** [Source](source.tex#L3531); [PDF p. 7](source.pdf#page=7).


This paper continues [[G+26b](#bib-finite)], but can be read independently. Both papers follow roughly the same strategy with the following differences. 

```latex
\text{[D018]}
```

 [D018](diagram-index.md#d018)

 In both cases, webs serve as a visual guide.


<a id="section-1f"></a>

### 1F. Computations and Lean verification

<!-- Source: source.tex lines 3540; PDF page 7. -->


<a id="s-lean"></a>


This paper builds on [[G+26b](#bib-finite), [LTV26](#bib-ltvbigdata)]. The accompanying computational tools and Lean formalization are collected in [[G+26a](#bib-golatuva-mu-code-2)]. The formalization verifies the main algebraic and cohomological argument relative to explicitly stated hypotheses from the literature; see [Remark 1F.1](#rem-verification).


<a id="rem-verification"></a>


**Remark 1F.1.** [Source](source.tex#L3549); [PDF p. 7](source.pdf#page=7).


The Lean formalization verifies the explicit affine family, the six-map web calculation, the gallery counts, the canonical correction and the row-sum identity for every $m\ge2$. It also formalizes the deduction of faithful absolutely irreducible modules with unbounded first cohomology. In addition, it verifies the rank-one correction and the five-term canonical expansion in [Section 5](#sec-aggregate-calibration), and proves the two ordinary KL polynomial identities for $m=2$, with lower endpoint $w_0$.

The remaining unformalized results from the literature are supplied as explicit hypotheses. These include the affine Coxeter realization, KL theory and positivity, canonical Schur bases and their compatibility with refinement, and flag-orbit classification and Hecke convolution. For the cohomological application, we use highest weight theory, restricted irreducibility, the eventual character formula, the KL-to-$H^1$ identification, rational cohomology via the Hochschild complex, comparison with finite group cohomology, and simplicity of the relevant projective special linear groups.

These background results are not formalized. The cohomological deduction retains the fixed trivial source and the stated characteristic bounds. References for the external inputs are [[And86](#bib-andersen), [AJS94](#bib-ajs), [BNP01](#bib-bnp), [BB05](#bib-bjornerbrentiaffine), [Cui14](#bib-cui), [Jan03](#bib-jantzen2003), [KL79](#bib-kl), [KL80](#bib-kl80), [Lüb20](#bib-luebeck), [Lus99](#bib-lusztigaffine), [Spr82](#bib-springer82), [Ste63](#bib-steinberg), [Ste16](#bib-steinbergyale), [Wil11](#bib-williamson)]. The citations are not necessarily to the original sources.

The Lean development also encodes the chosen web as a labeled graph and proves that its specified presentation evaluates to the six-map morphism used in the calculation.


<a id="acknowledgments"></a>

### Acknowledgments

<!-- Source: source.tex lines 3586; PDF page 7. -->


We thank the ANU Kioloa Coastal Campus, where the common interest of TG and DT was discovered at a workshop organized by Anthony Licata and Oded Yacobi. We thank Keeley Hoek for helping with translating C code into very efficient Rust code for computing $W$-graphs, and Lukas Lewark for making the `webdraw` program available for computing Kuperberg polynomials.

TG acknowledges funding by the Australian Government through ARC DP230102982. DT was supported by ARC Future Fellowship FT230100489 and asserts that no large language models were injured in the making of this paper (just one very tired human). P.V. is supported by FNRS (Belgium) Grant no. J.0235.26.


<a id="section-2"></a>

## 2. Annular webs and KL coefficients

<!-- Source: source.tex lines 3597; PDF page 8. -->


<a id="sec-dictionary"></a>


We define the web categories and their local calculus, identify their Hom spaces with Hecke and Schur maps, and use this identification to read affine KL coefficients from canonical webs. The ingredients are known; their systematic synthesis here is, to the best of our knowledge, new.


<a id="section-2a"></a>

### 2A. Drawing conventions

<!-- Source: source.tex lines 3605; PDF page 8. -->


<a id="subsec-drawing-conventions"></a>


Edges carry positive integer labels, called their thicknesses. A thin edge has label $1$ and is drawn in blue; its label is often omitted. A thick edge with label $a\ge2$ represents the $a$th quantum symmetric power of the defining representation, but no ambient rank is fixed. Labels specify thickness; printed line widths are schematic. Solid dots mark splits or merges, which conserve total thickness. Crossings have no vertex: a white gap marks the underpassing edge. 

```latex
\begin{array}{c@{\qquad}c@{\qquad}c@{\qquad}c}
\text{[D019]}
&
\text{[D020]}
&\text{[D021]}
&\text{[D022]}
\\[1ex]
\text{thin: label }1
&\text{thick: label }a\ge2
&\text{merge}
&\text{crossing}
\end{array}
```

 [D019](diagram-index.md#d019); [D020](diagram-index.md#d020); [D021](diagram-index.md#d021); [D022](diagram-index.md#d022)

 A straight strand is an identity. Zero labeled edges are deleted, and labels are often omitted if they can be recovered from the given data.

Planar and cut-open cylindrical diagrams are read from bottom to top; orientation arrows are usually omitted. If $f:\gamma\to\eta$ and $g:\eta\to\zeta$, stacking $g$ above $f$ gives $g\circ f$, so $f$ is applied first. Horizontal juxtaposition of planar webs is the tensor product. For $h:\delta\to\theta$, the conventions are as follows; boxes denote arbitrary webs and boundary labels denote sequences of edge labels. For annular diagrams, inputs lie on the inner circle and outputs on the outer circle: read outwards. Composition places $g$ outside $f$ and glues their common $\eta$-boundary, with cuts aligned. Red dashed lines mark boundaries and cuts; gray lines mark glued boundaries. The concentric bands below mean $f$ and $g$. 

```latex
g\circ f=
\text{[D023]}
\qquad
f\otimes h=
\text{[D024]}
\qquad
g\circ f=
\text{[D025]}.
```

 [D023](diagram-index.md#d023); [D024](diagram-index.md#d024); [D025](diagram-index.md#d025)

 Cutting the annulus open gives a rectangle with its vertical sides identified, and planar diagrams embed on such a rectangle. Matching seam labels mark continuations of the same edge at the same height. The cut fixes the start of each ordered boundary. For example, gluing the boundary $(3)$ gives 

```latex
\begin{gather*}
\text{[D026]}\ \circ\ \text{[D027]}
=\text{[D028]}
\quad\xleftrightarrow{\text{cut / glue}}\quad\text{[D029]}.
\end{gather*}
```

 [D026](diagram-index.md#d026); [D027](diagram-index.md#d027); [D028](diagram-index.md#d028); [D029](diagram-index.md#d029)

 The input and output are $(1,2)$. In an annular hole, a gray arrow connects an input label to its endpoint.

Freer drawings, with bent or horizontal segments, abbreviate upward webs. After isotopy, and cutting open in the annular case, all edges can be made to run upwards. We use no cups, caps or closed components. For example:

$\displaystyle \text{[D030]}
\quad\xleftrightarrow{\text{isotopy}}\quad
\text{[D031]}.$ [D030](diagram-index.md#d030); [D031](diagram-index.md#d031)


<a id="section-2b"></a>

### 2B. Symmetric webs

<!-- Source: source.tex lines 3730; PDF page 9. -->


Work over $\mathcal A=\mathbb Z[v,v^{-1}]$, with 

```latex
[a]=v^{a-1}+v^{a-3}+\cdots+v^{1-a},\qquad
[a]!=[1]\cdots[a],\qquad
\genfrac{[}{]}{0pt}{}{a+b}{a}=\frac{[a+b]!}{[a]![b]!},\qquad [0]!=1.
```


<a id="def-symmetric-webs"></a>


**Definition 2B.1.** [Source](source.tex#L3739); [PDF p. 9](source.pdf#page=9).


The symmetric web category $\mathsf{Web}$ is the $\mathcal A$-linear strict monoidal category with objects compositions $\gamma=(\gamma_1,\ldots,\gamma_k)$ of positive integers, tensor product concatenation and unit the empty composition. Its generators are splits, merges and invertible crossings, subject to the local relations below: 

```latex
\begin{gather*}
\iota_{a+b,(a,b)}=\text{[D032]},
\mu_{(a,b),a+b}=\text{[D033]},
H_{a,b}=
\text{[D034]},
H_{a,b}^{-1}=
\text{[D035]}.
\end{gather*}
```

 [D032](diagram-index.md#d032); [D033](diagram-index.md#d033); [D034](diagram-index.md#d034); [D035](diagram-index.md#d035)

 Here $a,b>0$. Write $\mathsf{Web}_N$ for total thickness $N=\sum_i\gamma_i$, and $\omega_N=(1,\ldots,1)$ for the all-thin boundary.

The defining relations are associativity, coassociativity and digon removal, and the Schur relation, for $a+b=c+d$:


<a id="eq-web-digon"></a>


```latex
\begin{gather}
\begin{gathered}
\text{[D036]}
=\text{[D037]},\quad
\text{[D038]}
=\text{[D039]},\quad
\text{[D040]}
=\genfrac{[}{]}{0pt}{}{a+b}{a}\text{[D041]},\\
\text{[D042]}
\ =\!
\sum_{\substack{0\le i\le a,\ 0\le j\le b\\i-j=a-c}}
v^{(a-i)(b-j)}\,
\text{[D043]}.
\end{gathered}
\end{gather}
```

 [D036](diagram-index.md#d036); [D037](diagram-index.md#d037); [D038](diagram-index.md#d038); [D039](diagram-index.md#d039); [D040](diagram-index.md#d040); [D041](diagram-index.md#d041); [D042](diagram-index.md#d042); [D043](diagram-index.md#d043)

 The crossing in a summand is $H_{i,j}$.

<a id="ai-statement-009"></a>


**Remark 2B.3.** [Source](source.tex#L3814); [PDF p. 9](source.pdf#page=9).


Webs have been around for a long time, see e.g. [[Yam89](#bib-yamada)]. The above is the integral presentation of [[LT26](#bib-latifitubbenhauer), Section~5], in the crossing normalization of [[Bru25](#bib-brundan), Theorem~1] and [[SSW25](#bib-ssw), (2.4)--(2.6)]. For exterior webs see [[CKM14](#bib-ckm), [Kup96](#bib-kuperberg)]; for symmetric and mixed webs see [[RT16](#bib-rosetubbenhauer), [TVW17](#bib-tvw), [Tub25](#bib-tu-qt)], among many others.

On $\omega_N$, let $H_i$ denote the positive crossing in positions $i,i+1$, and $b_i$ the thin merge followed by a split. Products of these diagrams mean stacking, with the rightmost factor applied first.


<a id="lem-thin-hecke-relations"></a>


**Lemma 2B.4.** [Source](source.tex#L3828); [PDF p. 9](source.pdf#page=9).


The Schur relation at $a=b=c=d=1$ gives


<a id="eq-thin-channel-normalization"></a>


```latex
\begin{gather}
b_i=\text{[D044]}
=\text{[D045]}+v\,\text{[D046]}\hspace{.6cm}\text{[D047]}
=H_i+v.
\end{gather}
```

 [D044](diagram-index.md#d044); [D045](diagram-index.md#d045); [D046](diagram-index.md#d046); [D047](diagram-index.md#d047)

 (Here $v$ means $v$ times the identity; the latter is often omitted in expressions.) The crossings satisfy Reidemeister II and III (arbitrary thickness; thin is illustrated below), and 

```latex
\begin{gather*}
\text{[D048]}=(v+v^{-1})\text{[D049]},\qquad
\text{[D050]}
=\text{[D051]}\hspace{.5cm}\text{[D052]},\qquad
\text{[D053]}
=\text{[D054]}.
\end{gather*}
```

 [D048](diagram-index.md#d048); [D049](diagram-index.md#d049); [D050](diagram-index.md#d050); [D051](diagram-index.md#d051); [D052](diagram-index.md#d052); [D053](diagram-index.md#d053); [D054](diagram-index.md#d054)

 Crossings can be expressed using splits and merges and can therefore be omitted as generators.

**Proof.**

The first identity is the two-term Schur relation. Contracting the middle digon gives $b_i^2=[2]b_i$, hence the quadratic relation. Distant crossings commute by juxtaposition. The remaining statements follow from [[LT26](#bib-latifitubbenhauer), Section~5] after changing normalization.

*End of proof.*

[Lemma 2B.4](#lem-thin-hecke-relations) gives the Hecke relations: 

```latex
\begin{gather*}
(H_i-v^{-1})(H_i+v)=0,\qquad
H_iH_j=H_jH_i\,(|i-j|>1)\qquad H_iH_jH_i=H_jH_iH_j\,(|i-j|=1).
\end{gather*}
```


<a id="lem-iterated-web-digons"></a>


**Lemma 2B.6.** [Source](source.tex#L3862); [PDF p. 10](source.pdf#page=10).


Nested digons contract as 

```latex
\begin{gather*}
\text{[D055]}
=\frac{[a+b]!}{[a]![b]!}\text{[D056]},
\qquad
\text{[D057]}
=\frac{[b+c]!}{[b]![c]!}\text{[D058]}.
\end{gather*}
```

 [D055](diagram-index.md#d055); [D056](diagram-index.md#d056); [D057](diagram-index.md#d057); [D058](diagram-index.md#d058)

 Both sides evaluate to $[a+b+c]!/([a]![b]![c]!)$ times the identity.

**Proof.**

Apply digon removal successively; retained strands are unchanged.

*End of proof.*


<a id="section-2c"></a>

### 2C. Annular webs

<!-- Source: source.tex lines 3879; PDF page 10. -->


<a id="subsec-affine-conventions"></a>


We now put the diagrams on an annulus.


<a id="def-annular-webs"></a>


**Definition 2C.1.** [Source](source.tex#L3883); [PDF p. 10](source.pdf#page=10).


The annular symmetric web category $\mathsf{AWeb}$ has the same objects as $\mathsf{Web}$ and morphisms given by $\mathcal A$-linear combinations of upward webs on a cylinder, modulo the local relations and isotopy with boundary fixed. The local relations also apply in disks meeting the cut. No Levi quotient is imposed. Write $\mathsf{AWeb}_N$ for the part of total thickness $N$.

A coil, displayed and defined by [Equation 2C.2](#fig-cut-guide) for thin edges (similarly for arbitrary thickness), moves a boundary edge across the cut. Coils exist in both directions and at every thickness. On $\omega_N$, let $X_i$ be the positive winding at position $i$; its inverse has a negative sign. Suppressing strands,


<a id="fig-cut-guide"></a>


```latex
\begin{gather}
\text{[D059]}=\text{[D060]}
\quad\xleftrightarrow{\text{cut / glue}}\quad\text{[D061]},\quad
X_i=\text{[D062]},\qquad X_i^{-1}=\text{[D063]}.
\end{gather}
```

 [D059](diagram-index.md#d059); [D060](diagram-index.md#d060); [D061](diagram-index.md#d061); [D062](diagram-index.md#d062); [D063](diagram-index.md#d063)


<a id="ai-statement-013"></a>


**Lemma 2C.3.** [Source](source.tex#L3905); [PDF p. 10](source.pdf#page=10).


We have


<a id="eq-invcoil"></a>


```latex
\begin{gather}
\text{[D064]}=\text{[D065]}=
\text{[D066]}.
\end{gather}
```

 [D064](diagram-index.md#d064); [D065](diagram-index.md#d065); [D066](diagram-index.md#d066)


**Proof.**

A visualization exercise.

*End of proof.*


<a id="lem-annular-relations"></a>


**Lemma 2C.5.** [Source](source.tex#L3923); [PDF p. 10](source.pdf#page=10).


Adjoining coils to $\mathsf{Web}$ together with [Equation 2C.4](#eq-invcoil) gives $\mathsf{AWeb}$. On a thin boundary, 

```latex
\begin{gather*}
X_iX_k=X_kX_i,\qquad H_iX_iH_i=X_{i+1},\qquad
H_iX_k=X_kH_i\quad(k\ne i,i+1).
\end{gather*}
```

 In pictures, (with arbitrary unrelated strands in between or to the left and right) 

```latex
\begin{gather*}
\text{[D067]}
=\text{[D068]},\qquad
\text{[D069]}
=\text{[D070]},\qquad
\text{[D071]}
=\text{[D072]}.
\end{gather*}
```

 [D067](diagram-index.md#d067); [D068](diagram-index.md#d068); [D069](diagram-index.md#d069); [D070](diagram-index.md#d070); [D071](diagram-index.md#d071); [D072](diagram-index.md#d072)

 Strands not involved in a relation remain fixed.

**Proof.**

The coil presentation is [[LTV23](#bib-ltv), Section~4A]. The displayed relations follow by moving coils across the cut.

*End of proof.*

<a id="ai-statement-015"></a>


**Definition 2C.6.** [Source](source.tex#L3948); [PDF p. 11](source.pdf#page=11).


Let $\rho_N$ be the positive cyclic rotation of $\omega_N$ (cf. [Equation 2C.7](#fig-rotation-in-webs)). Write $H_0$ for the crossing through the cut between the last and first thin positions. For $1\le a<N$, obtain $\beta_a$ from a reduced word for $w_a=[a+1,\ldots,N,1,\ldots,a]$ using positive thin crossings. A determinant dot on an $a$-edge denotes the product of its $a$ thin winding variables.

For three thin strands,


<a id="fig-rotation-in-webs"></a>


```latex
\begin{gather}
\begin{aligned}
\rho_3&=\text{[D073]}
\quad\leftrightsquigarrow\quad\text{[D074]}
\quad=\quad\text{[D075]},\\[1ex]
\rho_3^{-1}&=\text{[D076]}
\quad\leftrightsquigarrow\quad\text{[D077]}
\quad=\quad\text{[D078]}.
\end{aligned}
\end{gather}
```

 [D073](diagram-index.md#d073); [D074](diagram-index.md#d074); [D075](diagram-index.md#d075); [D076](diagram-index.md#d076); [D077](diagram-index.md#d077); [D078](diagram-index.md#d078)

 The words are $\rho_3=X_1H_1H_2$ and $\rho_3^{-1}=H_2^{-1}H_1^{-1}X_1^{-1}$.


<a id="lem-boundary-rotation"></a>
<a id="subsec-affine-rotation"></a>


**Lemma 2C.8.** [Source](source.tex#L3972); [PDF p. 11](source.pdf#page=11).


Boundary rotation satisfies


<a id="eq-web-rotation"></a>


```latex
\begin{gather}
\rho_N^a=(X_1\cdots X_a)\beta_a,\qquad
X_1=\rho_N H_{N-1}^{-1}\cdots H_1^{-1}.
\end{gather}
```

 Also $\rho_NH_i\rho_N^{-1}=H_{i+1}$, with indices modulo $N$. Thus $\beta_a$ moves the last $a$ input positions to the first $a$ output positions, which are then wound once.

On thick edges, use block crossings and determinant dots; for thickness two,

$\displaystyle
\text{[D079]}=[2]\hspace{4pt}\text{[D080]},
\qquad\text{[D081]}=[2]\hspace{4pt}\text{[D082]}.$ [D079](diagram-index.md#d079); [D080](diagram-index.md#d080); [D081](diagram-index.md#d081); [D082](diagram-index.md#d082)

The thick dots are $X_1X_2$ and its inverse. A vertex meeting the cut is obtained by rotating its edges away from the cut, applying the ordinary vertex, and rotating back.

**Proof.**

Cutting open the rotation gives the braid and winding words. The product of winding variables passes through a split or merge, leaving the digon scalar $[2]$ in the last display.

*End of proof.*

<a id="ai-statement-017"></a>


**Remark 2C.10.** [Source](source.tex#L4003); [PDF p. 11](source.pdf#page=11).


Annular webs, also called affine webs and other names in the literature, have been studied in various settings; see, e.g., [[CK18](#bib-ck), [FP14](#bib-fominpylyavskyy), [LTV23](#bib-ltv), [Que15](#bib-queffelec), [SW25](#bib-songwangwebs), [SSW25](#bib-ssw)].


<a id="section-2d"></a>

### 2D. Hecke and Schur categories

<!-- Source: source.tex lines 4007; PDF page 12. -->


<a id="subsec-affine-local-maps"></a>


The following is a reinterpretation of, e.g., [[Lus89](#bib-lusztigbernstein)], and many other sources.


<a id="def-affine-hecke-conventions"></a>


**Definition 2D.1.** [Source](source.tex#L4011); [PDF p. 12](source.pdf#page=12).


The extended affine symmetric group $\widehat S_N$ consists of bijections $w:\mathbb Z\to\mathbb Z$ with $w(i+N)=w(i)+N$. Its degree is $N^{-1}\sum_{i=1}^N(w(i)-i)$; the degree-zero subgroup is $W=\widetilde S_N$, and $W_0=\langle s_1,\ldots,s_{N-1}\rangle\cong S_N$. The rotation is $\tau=[2,3,\ldots,N,N+1]$.

The extended affine Hecke algebra $\mathcal H_{\rm aff}$ is the $\mathcal A$-algebra generated by $H_1,\ldots,H_{N-1}$ and $X_1^{\pm1},\ldots,X_N^{\pm1}$, subject to the braid, quadratic and Bernstein relations of [Lemma 2B.4](#lem-thin-hecke-relations) and [Lemma 2C.5](#lem-annular-relations), now read algebraically. Put 

```latex
\tau=X_1H_1\cdots H_{N-1},\qquad
H_0=\tau H_{N-1}\tau^{-1},\qquad
Q=v^{-2},\qquad H_i=vT_i.
```

 The $H_i$ with $1\le i<N$ generate the finite subalgebra $\mathcal H(W_0)$, and $(T_i+1)(T_i-Q)=0$. Write $H_w=v^{\ell(w)}T_w$ for the standard basis, with $T_\tau=\tau$. The degrees are $\deg H_i=0$ and $\deg X_i=\deg\tau=1$; the degree-zero subalgebra is the ordinary affine Hecke algebra.


<a id="def-spherical-modules"></a>


**Definition 2D.2.** [Source](source.tex#L4039); [PDF p. 12](source.pdf#page=12).


For a finite parabolic $P$ with longest element $w_P$, put 

```latex
x_P=\sum_{w\in P}T_w,\qquad
C_P=v^{\ell(w_P)}x_P,\qquad
h_P=v^{\ell(w_P)}\sum_{w\in P}Q^{\ell(w)}.
```

 The spherical right module is $\mathcal M_P=C_P\mathcal H_{\rm aff}=x_P\mathcal H_{\rm aff}$; its generator satisfies $C_PH_i=v^{-1}C_P$ for $s_i\in P$. For a composition $\gamma$, let $W_\gamma$ permute its consecutive blocks and write $\mathcal M_\gamma=\mathcal M_{W_\gamma}$, $x_\gamma=x_{W_\gamma}$ and $C_\gamma=C_{W_\gamma}$.


<a id="def-affine-schur-maps"></a>


**Definition 2D.3.** [Source](source.tex#L4054); [PDF p. 12](source.pdf#page=12).


The affine Schur category $\mathsf{Schur}_N$ has compositions of $N$ as objects and morphisms $\Hom_{\mathsf{Schur}_N}(\gamma,\alpha) =\Hom_{\mathcal H_{\rm aff}}(\mathcal M_\gamma,\mathcal M_\alpha),$ with composition of module maps.


<a id="lem-vertex-normalization"></a>


**Lemma 2D.4.** [Source](source.tex#L4061); [PDF p. 12](source.pdf#page=12).


There is an $\mathcal A$-linear isomorphism of categories $\Phi_N:\mathsf{AWeb}_N\to\mathsf{Schur}_N$, fixing the boundary compositions. In particular,


<a id="eq-web-schur-hom"></a>


```latex
\begin{gather}
\Phi_N:\Hom_{\mathsf{AWeb}}(\gamma,\alpha)
\xrightarrow{\ \sim\ }
\Hom_{\mathcal H_{\rm aff}}(\mathcal M_\gamma,\mathcal M_\alpha).
\end{gather}
```

 For finite parabolics $L\subset P$, its split and merge maps are 

```latex
\iota_{P,L}:\mathcal M_P\longrightarrow\mathcal M_L,
C_Ph\longmapsto C_Ph,\quad
\mu_{L,P}:\mathcal M_L\longrightarrow\mathcal M_P,
C_Lh\longmapsto C_Ph.
```

 For adjacent edges $(a,b)$, take $P=S_{a+b}$ and $L=S_a\times S_b$; a vertex across the cut is transported by rotation as in [Lemma 2C.8](#lem-boundary-rotation).

There is an algebra embedding, in fact an isomorphism, 

```latex
\begin{gather*}
\jmath_N:\mathcal H_{\rm aff}
\xrightarrow{\ \sim\ }\operatorname{End}_{\mathsf{AWeb}}(\omega_N).
\end{gather*}
```

 It sends $H_i$ to the thin crossing in positions $i,i+1$, $X_i^{\pm1}$ to the corresponding winding dot, and $\tau$ to $\rho_N$. Thus $H_{w_a}$ is represented by $\beta_a$. Its finite restriction is $\mathcal H(W_0)\cong\operatorname{End}_{\mathsf{Web}}(\omega_N)$.

**Proof.**

The isomorphism is [[SSW25](#bib-ssw), Theorem~4.16, Proposition~4.18(1)], with $q=v$; see also [[Gre99](#bib-greenaffine)], [[TVW17](#bib-tvw), Theorem~3.22] and [[Bru25](#bib-brundan)]. To fix the vertex normalization, let $P^L$ be the minimal right-coset representatives for $P/L$. Then 

```latex
\sigma_{P/L}=\sum_{x\in P^L}
v^{\ell(w_P)-\ell(w_L)-\ell(x)}H_x,\qquad
C_P=\sigma_{P/L}C_L=C_L\sigma_{P/L}^{*},
\qquad H_w^*=H_{w^{-1}}.
```

 This gives the split as an inclusion of right ideals. The induced-module presentation makes the merge well-defined. Both maps are integral, and the shuffle expansion gives 

```latex
\mu_{L,P}\circ\iota_{P,L}
=\frac{h_P}{h_L}\,\operatorname{id}_{\mathcal M_P},
\qquad h_{S_a}=[a]!.
```

 For adjacent edges this is exactly the digon scalar in [Equation 2B.2](#eq-web-digon). These are the normalized maps of [[TVW17](#bib-tvw), [LT26](#bib-latifitubbenhauer)] and [[SSW25](#bib-ssw), (3.21)--(3.22)]. The thin boundary has $\mathcal M_{\omega_N}=\mathcal H_{\rm aff}$. Since these are right modules, $h$ acts by left multiplication $L_h$, and $L_a\circ L_b=L_{ab}$. Apply [Equation 2D.5](#eq-web-schur-hom); the finite case is analogous.

*End of proof.*

Henceforth we identify Schur maps with webs using $\Phi_N$. The algebraic degree is the signed, thickness-weighted-winding across the cut, so this identification also respects degree.


<a id="section-2e"></a>

### 2E. Standard and canonical bases

<!-- Source: source.tex lines 4127; PDF page 13. -->


We recall the standard and canonical bases of affine Schur maps, with the normalization needed below. Under the identification in [Lemma 2D.4](#lem-vertex-normalization), the latter can be viewed as canonical annular webs.


<a id="def-hecke-kl-basis"></a>


**Definition 2E.1.** [Source](source.tex#L4134); [PDF p. 13](source.pdf#page=13).


The Hecke bar fixes $\tau$, sends $v$ to $v^{-1}$ and $H_i$ to $H_i^{-1}$. We use the KL normalization $C_w=v^{\ell(w)}\sum_{y\le w}P_{y,w}(v^{-2})T_y.$ In particular, $C_{w_P}=C_P$ and $C_{s_i}=H_i+v$. On Schur maps the induced bar is $\overline f(C_\gamma h)=\overline{f(C_\gamma)}h$.

Thus $C_{s_i}=b_i$ is the merge-split web of [Equation 2B.5](#eq-thin-channel-normalization). Moreover, in pictures, 

```latex
\overline{\text{[D083]}}
=\text{[D084]},\qquad
\overline{\text{[D085]}}
=\text{[D086]},\qquad
\overline{\text{[D087]}}=\text{[D088]},\qquad
\overline{\rho_N}=\rho_N.
```

 [D083](diagram-index.md#d083); [D084](diagram-index.md#d084); [D085](diagram-index.md#d085); [D086](diagram-index.md#d086); [D087](diagram-index.md#d087); [D088](diagram-index.md#d088)


For thick crossings, the same rule reads $\overline{H_{a,b}}=H_{b,a}^{-1}$. For winding dots, [Equation 2C.9](#eq-web-rotation) gives $\overline{X_1}=\rho_N H_{N-1}\cdots H_1$. For example, on three thin strands,

$\displaystyle
\overline{\text{[D089]}}
=\text{[D090]}.$ [D089](diagram-index.md#d089); [D090](diagram-index.md#d090)

The other positions and inverse dots follow from the annular relations.


<a id="def-schur-bases"></a>


**Definition 2E.2.** [Source](source.tex#L4169); [PDF p. 13](source.pdf#page=13).


For three-position boundaries $\alpha,\gamma$, double cosets are indexed by periodic matrices $A=(a_{ik})_{i,k\in\mathbb Z}$. Their entries are nonnegative, each row and column has finite support, and 

```latex
a_{i+3,k+3}=a_{ik},\qquad
\sum_k a_{ik}=\alpha_i,\qquad
\sum_i a_{ik}=\gamma_k.
```

 Here the boundaries are extended periodically. Rows record target edges and columns source edges in the unwrapped strip; shifting both indices by three moves to the next copy.

Put $L_\gamma=\ell(w_{0,\gamma})$. For the double coset $W_\alpha d(A)W_\gamma$, let $d(A)$ and $w_A^+$ be its shortest and longest representatives. Define $\phi_A(x_\gamma h)=\sum_{w\in W_\alpha d(A)W_\gamma}T_wh,$ and the normalized standard and canonical maps by 

```latex
[A]_v=v^{\ell(w_A^+)-L_\gamma}\phi_A,\qquad
\theta_A(C_\gamma)=C_{w_A^+}.
```

 We order matrices by Bruhat order on their longest representatives, and put 

```latex
\operatorname{dimdeg}(A)=
\sum_{\substack{1\le i\le3,\ k\le i\\j<l}}a_{ij}a_{kl}.
```

 The sum is finite by periodicity and finite support.


<a id="lem-affine-schur-dictionary"></a>


**Lemma 2E.3.** [Source](source.tex#L4201); [PDF p. 13](source.pdf#page=13).


The $[A]_v$ and $\theta_A$ form the standard and canonical bases, respectively. Moreover, $\operatorname{dimdeg}(A)=\ell(w_A^+)-L_\gamma,$ and the change of basis is


<a id="eq-exact-schur-dictionary"></a>


```latex
\begin{gather}
\theta_A=\sum_{Z:\,w_Z^+\le w_A^+}
v^{\ell(w_A^+)-\ell(w_Z^+)}
P_{w_Z^+,w_A^+}(v^{-2})[Z]_v.
\end{gather}
```

 $\theta_A$ is the unique bar invariant element with leading term $[A]_v$ and proper coefficients in $v\mathbb Z[v]$.

**Proof.**

The degree formula is [[DF15](#bib-dufu), (2.0.3)] with parameter $v^{-1}$, or [[Cui14](#bib-cui), Lemma~7.2] with $t=v^{-1}$. Grouping the KL expansion into double cosets gives the change of basis and triangularity [[Cui14](#bib-cui), Lemma~3.1, Theorem~3.1, (3.4)--(3.5)]. Bar invariance follows from that of $C_{w_A^+}$.

*End of proof.*

There is also a diagrammatic description of the standard basis. Write $\iota_{\gamma,\omega_N}$ and $\mu_{\omega_N,\alpha}$ for the total split and merge, and put $I_A=W_\alpha\cap d(A)W_\gamma d(A)^{-1}$. Then 

```latex
h_{I_A}[A]_v
=\mu_{\omega_N,\alpha}\circ\jmath_N(H_{d(A)})
\circ\iota_{\gamma,\omega_N}
=\text{[D091]}.
```

 [D091](diagram-index.md#d091)

 This is a diagrammatic sandwich, in the spirit of sandwich cellularity as in, e.g., [[Tub24](#bib-sandwich)]. Indeed, parabolic multiplication gives 

```latex
C_\alpha H_{d(A)}C_\gamma
=h_{I_A}\,v^{\ell(w_A^+)}
\sum_{w\in W_\alpha d(A)W_\gamma}T_w,
```

 and the two sides define the same map on $C_\gamma$. The factor $h_{I_A}$ accounts for repeated symmetrization at the overlap. Canonical webs are bar invariant triangular combinations of these standard webs; they need not be single diagrams.

<a id="ai-statement-025"></a>


**Remark 2E.5.** [Source](source.tex#L4268); [PDF p. 14](source.pdf#page=14).


These bases come from [[BLM90](#bib-blm), [Du92](#bib-du), [Lus99](#bib-lusztigaffine)], in the induced-trivial convention of [[Deo87](#bib-deodhar)]; see also [[McG03](#bib-mcgerty)] for a useful summary. They differ from the elementary ribbon basis of [[SSW25](#bib-ssw), Theorem~4.16]: a composite web must be expanded in the standard basis before one can read its KL coefficients. An analogous distinction appears in the classical web calculus: Khovanov--Kuperberg (KK) showed that the $\mathfrak{sl}_3$ web basis is not in general dual canonical [[KK99](#bib-kk99)].

<a id="ai-statement-026"></a>


**Example 2E.6.** [Source](source.tex#L4279); [PDF p. 14](source.pdf#page=14).


Already on three thin strands, a composite web can require a canonical correction: 

```latex
\underbrace{\text{[D092]}}_{b_1b_2b_1}
-\underbrace{\text{[D093]}}_{b_1}
=\underbrace{\text{[D094]}}_{C_{s_1s_2s_1}}.
```

 [D092](diagram-index.md#d092); [D093](diagram-index.md#d093); [D094](diagram-index.md#d094)

 Indeed, expanding $b_i=H_i+v$ and applying the quadratic relation gives 

```latex
b_1b_2b_1-b_1
=H_{s_1s_2s_1}+v(H_{s_1s_2}+H_{s_2s_1})
 +v^2(H_{s_1}+H_{s_2})+v^3=C_{S_3}.
```

 The final web is the total merge followed by the total split, which represents $C_{S_3}$ by [Lemma 2D.4](#lem-vertex-normalization). Thus even a bar invariant composite need not itself be canonical.


<a id="def-dictionary-corner"></a>


**Definition 2E.7.** [Source](source.tex#L4299); [PDF p. 14](source.pdf#page=14).


Return to $N=2m+1$ and put $\lambda=(N,0,0)$ and $\nu=(m,1,m)$. We work in the degree-zero part of 

```latex
\mathcal C_m=\Hom_{\mathcal H_{\rm aff}}
(x_\lambda\mathcal H_{\rm aff},x_\nu\mathcal H_{\rm aff}).
```

 The zeros pad the source $(N)$; intermediate boundaries may have five edges. For $1\le j\le m$, define the following matrices. We display rows $1,2,3$ and columns $-2,1,4$, in that order: 

```latex
A_{j;m}=\begin{pmatrix}1&m-j&j-1\\0&1&0\\j-1&m-j&1\end{pmatrix},
\qquad
B_m=\begin{pmatrix}0&m&0\\0&1&0\\0&m&0\end{pmatrix}.
```

 All other entries in these rows vanish; extend periodically. The row sums are $\nu$, and the full column sums are $\lambda$. Indeed, the three displayed columns of $A_{j;m}$ sum to $j,N-2j,j$. Since their indices are all congruent to $1$ modulo $3$, their periodic translates give the required full column sums.

Write $u=u_{j;m}$ and $C=C_{j;m}=uw_0$, with shifts $\delta_i=\delta_i(j)$ as in the introduction.


<a id="lem-dictionary-endpoints"></a>


**Lemma 2E.8.** [Source](source.tex#L4326); [PDF p. 14](source.pdf#page=14).


The longest representatives of $A_{j;m}$ and $B_m$ are $w_{A_{j;m}}^+=C=uw_0,\qquad w_{B_m}^+=w_0.$ Their degrees are 

```latex
\operatorname{dimdeg}(A_{j;m})=\ell(u)
=2j(N-j)-2(m-j)-3=:D_{j;m},
\qquad
\operatorname{dimdeg}(B_m)=0.
```


<a id="fig-spherical-boundary"></a>


```latex
\begin{gather}
\begin{minipage}[c]{.53\linewidth}
Finally, the ordinary split through the intermediate edge
$m+1$ is both standard and canonical:
\end{minipage}\qquad
[B_m]_v=\theta_{B_m}=\text{[D095]}.
\end{gather}
```

 [D095](diagram-index.md#d095)


**Proof.**

The row blocks for $\nu$ are 

```latex
R_1^\nu=[1,m],\qquad R_2^\nu=\{m+1\},\qquad
R_3^\nu=[m+2,N],\qquad R_{i+3}^\nu=R_i^\nu+N.
```

 Define source blocks for $\lambda$ similarly. Relative position is $a_{ik}=|R_i^\nu\cap C(R_k^\lambda)|$. The nonempty source blocks have indices $1+3t$ and contain $1+tN,\ldots,N+tN$. A residue $r\in R_i^\nu$ contributes to column $1-3\delta_r$. Counting gives $A_{j;m}$; zero shifts give $B_m$.

To identify the longest representatives, note that $u$ has increasing window. Hence $C=uw_0$ has all finite right descents and $\ell(C)=\ell(u)+\ell(w_0)$. If $p(r)$ is the position of $r+N\delta_r$ in the window of $u$, then $C^{-1}(r)=N+1-p(r)-N\delta_r.$ Within $[1,m]$ and $[m+2,N]$, the shifts are weakly increasing. Equal adjacent shifts give $p(r)<p(r+1)$; increasing shifts make $C^{-1}$ strictly decrease through $-N\delta_r$. Thus every generator of $W_\nu$ is a left descent of $C$. At the omitted finite generators the shifts drop from $1$ to $0$ and from $0$ to $-1$, so neither is a left descent. The unique element with all prescribed parabolic left and right descents is the longest representative.

It remains to compute the length. In the increasing window inversion formula, negative-zero and zero-positive shift pairs each contribute $(j-1)(N-2j)+(m-j)$, while negative-positive pairs contribute $2j^2-1$. All other pairs contribute zero. Adding gives the asserted length and degrees.

For $B_m$, the canonical map and the iterated split all fix $C_{w_0}$, proving the last claim.

*End of proof.*

For a basis vector $b$, write $[b]f$ for its coefficient in $f$, and let $[v]$ extract the coefficient of $v$. A splitter drawn inside the brackets means its coefficient in the normalized standard basis. This denotes coefficient extraction, not composition or closure.


<a id="cor-dictionary-readout"></a>


**Proposition 2E.10.** [Source](source.tex#L4389); [PDF p. 15](source.pdf#page=15).


The required affine KL coefficient is read from the canonical web by 

```latex
\big[[B_m]_v\big]\theta_{A_{j;m}}
=v^{D_{j;m}}P_{w_0,uw_0}(v^{-2}).
```

 In particular, $[v]\big(\big[[B_m]_v\big]\theta_{A_{j;m}}\big)=\mu_{j;m}.$

**Proof.**

Apply [Equation 2E.4](#eq-exact-schur-dictionary) with $Z=B_m$. Since $D_{j;m}$ is odd, the term of degree $(D_{j;m}-1)/2$ in the KL polynomial becomes the coefficient of $v$.

*End of proof.*

As we will see in [Section 3](#sec-algebraic-gallery), the standard coefficients of our main web are straightforward to compute, leaving only the base change to the canonical basis (which we carry out in [Section 4](#sec-algebraic-relevance)). Afterwards, [Proposition 2E.10](#cor-dictionary-readout) directly yields the required coefficient.


<a id="section-3"></a>

## 3. The main web

<!-- Source: source.tex lines 4408; PDF page 15. -->


<a id="sec-algebraic-gallery"></a>


The following is the main construction.


<a id="section-3a"></a>

### 3A. Six split and merge maps

<!-- Source: source.tex lines 4412; PDF page 15. -->


<a id="s-mainweb"></a>


Fix $m\ge2$ and $N=2m+1$. Set 

```latex
\Lambda=(N),\quad V=(m,1,m),\quad J=(2m,1),\quad
L=(1,m-1,1,m-1,1),\quad K=(1,N-2,1).
```

 We also use these letters for the corresponding finite parabolic subgroups, specified in the next subsection; $\Lambda$ corresponds to $W_0$.

The annular web $\mathcal R_m$ is the composite 

```latex
\begin{gather*}
\Lambda\xrightarrow{\text{(a)}}V
\xrightarrow{\text{(b)}}J
\xrightarrow{\text{(c)}}L
\xrightarrow{\text{(d)}}K
\xrightarrow{\text{(e)}}L
\xrightarrow{\text{(f)}}V.
\end{gather*}
```

 The six maps are the following.


```latex
\begin{gather*}
\begin{gathered}
\begin{array}{c@{\hspace{.75cm}}c@{\hspace{.75cm}}c}
\text{(a) Split}&\text{(b) Annular merge}&
\text{(c) Annular split}\\[1ex]
\text{[D096]}&\text{[D097]}&\text{[D098]}\\[.7ex]
\Lambda\to V&V\to J&J\to L
\end{array}\\[1.5ex]
\begin{array}{c@{\hspace{.75cm}}c@{\hspace{.75cm}}c}
\text{(d) Middle merges}&\text{(e) Middle splits}&
\text{(f) Outer merges}\\[1ex]
\text{[D099]}&\text{[D100]}&\text{[D101]}\\[.7ex]
L\to K&K\to L&L\to V
\end{array}
\end{gathered}
\end{gather*}
```

 [D096](diagram-index.md#d096); [D097](diagram-index.md#d097); [D098](diagram-index.md#d098); [D099](diagram-index.md#d099); [D100](diagram-index.md#d100); [D101](diagram-index.md#d101)


<a id="fig-continuous-m2"></a>


```latex
\begin{gather}
\begin{minipage}[c]{.23\linewidth}\raggedright
Stacking the six maps gives the full web, with the successive
boundaries marked on the left:
\end{minipage}\quad
\mathcal R_m=\text{[D102]}.
\end{gather}
```

 [D102](diagram-index.md#d102)

 The blue unit strands exposed in (c) pass unchanged through (d)--(e) and rejoin in (f).


<a id="section-3b"></a>

### 3B. The symmetrizer expression

<!-- Source: source.tex lines 4462; PDF page 16. -->


By [Lemma 2D.4](#lem-vertex-normalization), a split $P\to Q$, $Q\subset P$, is the inclusion $M_P\to M_Q$; the reverse merge sends $C_Qh$ to $C_Ph$. Thus (a)--(f) give the parabolic chain $W_0\supset V\subset J\supset L\subset K\supset L\subset V$, where $W_0=\langle s_1,\ldots,s_{N-1}\rangle$ and 

```latex
\begin{aligned}
J&=\langle s_i:i\in\mathbb Z/N\mathbb Z
\setminus\{m,m+1\}\rangle,
& K&=\langle s_2,\ldots,s_{N-2}\rangle,\\
V&=W_0\cap J,
& L&=J\cap K=K\cap V.
\end{aligned}
```

 Their types are $V\cong S_m\times S_m$, $J\cong S_{2m}$, $K\cong S_{2m-1}$ and $L\cong S_{m-1}\times S_{m-1}$. The $2m$-edge of $J=(2m,1)$ crosses the cut, so $J$ contains $s_0$ but is finite, with symmetrizer $C_J=\tau^{m+1}C_{\langle s_1,\ldots,s_{N-2}\rangle}\tau^{-(m+1)}$. By [Lemma 2C.8](#lem-boundary-rotation), (b)--(c) are ordinary parabolic maps transported across the cut, hence integral of degree zero.


<a id="lem-main-symmetrizer"></a>


**Lemma 3B.1.** [Source](source.tex#L4486); [PDF p. 16](source.pdf#page=16).


Identify the right spherical module with $C_{W_0}\mathcal H_{\rm aff}$ by $M_e\mapsto C_{W_0}$, where $M_eH_i=v^{-1}M_e$ for $1\le i<N$. In the inverse-permutation convention,


<a id="eq-marked-symmetrizer"></a>


```latex
\begin{gather}
\mathcal R_m=\frac{M_eC_JC_KC_V}{d_m},\qquad
d_m=h_Vh_L^2=[m]!^2[m-1]!^4.
\end{gather}
```

 This quotient is integral and bar invariant.

**Proof.**

Evaluate the six maps of [Section 3A](#s-mainweb) on $C_{W_0}$ using [Lemma 2D.4](#lem-vertex-normalization). Over $\mathbb Q(v)$, their composite is $C_VC_KC_JC_{W_0}/(h_Vh_L^2)$. The overlaps $W_0\cap J=V$, $J\cap K=L$ and $K\cap V=L$ give the three digon factors. Thus the quotient represents the six integral maps, and inversion reverses the product as stated. Every $C_P$ and $h_P$ is bar invariant.

*End of proof.*

<a id="ai-statement-031"></a>


**Remark 3B.3.** [Source](source.tex#L4507); [PDF p. 17](source.pdf#page=17).


The use of parabolic chains is classical in the Schur algebroid; see [[Wil11](#bib-williamson)]. Elias--Ko relate this combinatorics to ordinary type $A$ webs via an associated graded construction [[EK23](#bib-eliasko)]. For products of parabolic KL elements and their canonical corrections, see also [[AS21](#bib-agrawalsotirov)].

Write $C_A,\Delta_A$ for the images of $\theta_A,[A]_v$ under $H_w^*=H_{w^{-1}}$. Then $C_B=M_e$ and $[\Delta_A]C_Z=[[A]_v]\theta_Z$. Indeed, 

```latex
[A]_v(C_{W_0})=v^{\ell(w_A^+)}
\sum_{w\in Vd(A)W_0}T_w,
```

 and $*$ replaces this coset by $W_0d(A)^{-1}V$ without changing the scalar. The anti-involution $*$ sends $H_w$ to $H_{w^{-1}}$ and reverses products. The bar sends $H_w$ to $H_{w^{-1}}^{-1}$, sends $v$ to $v^{-1}$, and preserves products.


<a id="section-3c"></a>

### 3C. Counting flags

<!-- Source: source.tex lines 4529; PDF page 17. -->


Schur convolution counts intermediate flags [[BLM90](#bib-blm), [Lus99](#bib-lusztigaffine)]. For $\mathcal R_m$, we choose a line, a hyperplane and an $m$-space inside an $(m+1)$-space in an $N$-dimensional quotient.


<a id="def-gallery-flags"></a>


**Definition 3C.1.** [Source](source.tex#L4535); [PDF p. 17](source.pdf#page=17).


Let $A$ have period three, row sizes $(m,1,m)$ and support in columns $-2,1,4$, with these indices retained under inversion. Set 

```latex
\begin{gathered}
r=\sum_{i=1}^3 a_{i,-2}=\sum_{i=1}^3 a_{i,4},\quad \ell=m-r,
\quad d_A=\operatorname{dimdeg}(A),\\
a=a_{1,-2},\quad b=a_{1,-2}+a_{2,-2},\quad
c=m-a_{1,4},\quad d=m+1-a_{1,4}-a_{2,4}.
\end{gathered}
```

 The relative rank $r$ counts the shifts of each sign. In an $N$-dimensional space $E$, fix flags $I_0\subset K_0$ and $F\subset F'$ with 

```latex
\begin{gathered}
\dim(I_0,K_0)=(r,N-r),\qquad\dim(F,F')=(m,m+1),\\
\dim(I_0\cap F)=a,\quad\dim(I_0\cap F')=b,\quad
\dim(K_0\cap F)=c,\quad\dim(K_0\cap F')=d.
\end{gathered}
```

 A gallery is a flag $L\subset I\subset K\subset H$ of dimensions $(1,m,m+1,N-1)$, with $L\subset F$, $F'\subset H$ and $I_0\subset I\subset K\subset K_0$.

Write $[n]_Q=1+Q+\cdots+Q^{n-1}$, with $[0]_Q=0$, and set $\genfrac{[}{]}{0pt}{}{n}{k}_Q=0$ for $k<0$ or $k>n$. The choices of $L,H$ split into four cases: 

```latex
\begin{array}{c|cc}
&0&1\\\hline
\text{line }(\epsilon)&L\subset I_0&L\not\subset I_0\\
\text{hyperplane }(\eta)&H\supset K_0&H\not\supset K_0
\end{array}
\qquad
\begin{aligned}
\mathsf L_0&=[a]_Q,&\mathsf L_1&=[c]_Q-[a]_Q,\\
\mathsf H_0&=[d-\ell-1]_Q,&
\mathsf H_1&=[\ell+b]_Q-[d-\ell-1]_Q.
\end{aligned}
```

 Infeasible cases contribute zero. Put


<a id="eq-gallery-gaussian"></a>


```latex
\begin{gather}
F_A(Q)=\sum_{\epsilon,\eta\in\{0,1\}}
\mathsf L_\epsilon\mathsf H_\eta
\genfrac{[}{]}{0pt}{}{N-2r-\epsilon-\eta}{m-r-\epsilon}_Q
[m+1-r-\eta]_Q.
\end{gather}
```


<a id="lem-finite-flag-count"></a>


**Lemma 3C.3.** [Source](source.tex#L4585); [PDF p. 17](source.pdf#page=17).


Over $\mathbb F_Q$, the number of galleries is $F_A(Q)$.

**Proof.**

The $\mathsf L_\epsilon$ choices of $L$ and $\mathsf H_\eta$ choices of $H$ are independent since $L\subset F\subset F'\subset H$. The remaining flag $I_0+L\subset I\subset K\subset K_0\cap H$ has endpoint dimensions $r+\epsilon$ and $N-r-\eta$: 

```latex
\text{[D103]}
```

 [D103](diagram-index.md#d103)


Choose $I/(I_0+L)$ in the quotient of dimension $N-2r-\epsilon-\eta$, then the line $K/I$. These give the Gaussian and quantum-integer factors in [Equation 3C.2](#eq-gallery-gaussian).

*End of proof.*

The same count has a local web calculation. Put $n=N-2r-\epsilon-\eta$ and $k=m-r-\epsilon$ in a feasible case. The quotient flag has dimensions $k,k+1$ in dimension $n$. Choosing the $(k+1)$-space first gives the left web; choosing the $k$-space first gives the right web: 

```latex
\text{[D104]}
=\text{[D105]}
=\genfrac{[}{]}{0pt}{}{n}{k}[n-k]\,\text{[D106]}.
```

 [D104](diagram-index.md#d104); [D105](diagram-index.md#d105); [D106](diagram-index.md#d106)

 The first equality is associativity and coassociativity; the second removes the two digons. Write $\langle W\rangle$ for the scalar multiplying the straight strand in such an ordinary split--merge web $W$. This is an open-web evaluation, not a trace. Multiplying the displayed scalar by $v^{-k(n-k)-(n-k-1)}$ gives $\genfrac{[}{]}{0pt}{}{n}{k}_Q[n-k]_Q$, exactly the two remaining factors in [Equation 3C.2](#eq-gallery-gaussian). Delete a zero edge at $k=0$ or $k=n-1$; infeasible cases contribute zero.


<a id="prop-gallery-standard"></a>


**Proposition 3C.4.** [Source](source.tex#L4635); [PDF p. 18](source.pdf#page=18).


Put $D=2m^2+2m-3$. The standard coefficient of $\mathcal R_m$ is 

```latex
\big[[A]_v\big]\mathcal R_m=v^{D-d_A}F_A(v^{-2}).
```

 All standards outside the support of [Definition 3C.1](#def-gallery-flags) vanish. At the source $B=B_m$,


<a id="eq-gallery-source"></a>


```latex
\begin{gather}
\big[[B]_v\big]\mathcal R_m
=v^D[m]_{v^{-2}}^3\genfrac{[}{]}{0pt}{}{2m-1}{m-1}_{v^{-2}}
=v^{m^2}[m]^3\genfrac{[}{]}{0pt}{}{2m-1}{m-1}_{\rm sym},
\end{gather}
```

 where $\genfrac{[}{]}{0pt}{}{n}{k}_{\rm sym}=v^{k(n-k)}\genfrac{[}{]}{0pt}{}{n}{k}_{v^{-2}}$. The coefficient at $A_{m;m}$ is one.

**Proof.**

Let $Q$ be a prime power. A lattice is a free rank $N$ $\mathbb F_Q[[t]]$-submodule of $\mathbb F_Q((t))^N$ spanning that space. A complete periodic chain has $\Lambda_i\subset\Lambda_{i+1}$, $\dim(\Lambda_{i+1}/\Lambda_i)=1$ and $\Lambda_{i+N}=t^{-1}\Lambda_i$; position $i$ has type $i$ modulo $N$. Partial chains retain selected positions.

The parabolics $W_0,J,K,V$ fix types $0$; $m,m+1$; $0,1,N-1$; and $0,m,m+1$, respectively. The convolution counts chains from $\Lambda$ to $(\Lambda',\widetilde F,\widetilde F')$ satisfying 

```latex
\begin{gathered}
\text{[D107]}\\[-.1ex]
\dim(\widetilde I/\Lambda)=m,\quad
\dim(\widetilde K/\Lambda)=m+1,\quad
\dim(\widetilde L/\Lambda')=1,\quad
\dim(\widetilde H/\Lambda')=N-1.
\end{gathered}
```

 [D107](diagram-index.md#d107)

 The endpoint lattices have equal determinant degree, so $\dim(\widetilde I/\Lambda')=m$ and $\dim(\widetilde K/\Lambda')=m+1$. Refining the common facets to complete chambers introduces their Poincaré factors $h_V,h_L,h_L$; forgetting these refinements cancels the denominator in [Equation 3B.2](#eq-marked-symmetrizer).

The inclusions force $\Lambda\subset t^{-1}\Lambda'$ and $\Lambda'\subset t^{-1}\Lambda$. Hence the relative exponents are $-1,0,1$, with $r$ of each nonzero sign, proving the support assertion. In $E=t^{-1}\Lambda'/\Lambda'$, set 

```latex
I_0=(\Lambda+\Lambda')/\Lambda',\qquad
K_0=(t^{-1}\Lambda\cap t^{-1}\Lambda')/\Lambda',\qquad
(F,F')=(\widetilde F,\widetilde F')/\Lambda'.
```


The quotient has the dimensions and intersections of [Definition 3C.1](#def-gallery-flags), and its galleries are counted by $F_A(Q)$. The count over all finite fields gives the polynomial identity for Hecke multiplication.

For $\ell_P=\ell(w_P)$, we have $\ell_J=m(2m-1)$, $\ell_K=(2m-1)(m-1)$, $\ell_V=m(m-1)$ and $\ell_L=(m-1)(m-2)$. The normalization exponent is therefore $\ell_J+\ell_K+\ell_V-\ell_V-2\ell_L=D$; the output standard removes $d_A$. At $B$, $r=a=b=0$, $c=m$, $d=m+1$, and only $(\epsilon,\eta)=(1,1)$ contributes, giving [Equation 3C.5](#eq-gallery-source). At $A_{m;m}$ the intermediate flags are forced, so $F_A=1$ and $d_A=D$.

*End of proof.*

Each individual choice is likewise a digon scalar. For $d\ge1$ and $0\le k\le n$, 

```latex
[d]_Q=v^{1-d}\left\langle\,\text{[D108]}\,\right\rangle,\qquad
\genfrac{[}{]}{0pt}{}{n}{k}_Q=v^{-k(n-k)}\left\langle\,\text{[D109]}\,\right\rangle.
```

 [D108](diagram-index.md#d108); [D109](diagram-index.md#d109)

 At $k=0,n$, delete the zero edge to obtain an identity. Thus $F_A$ uses products and differences of digon scalars; at $B$, 

```latex
\begin{array}{c@{\qquad}c}
\big[[B]_v\big]\mathcal R_m&\big[[B_2]_v\big]\mathcal R_2\\[.4ex]
{}=v^{m^2}\left\langle\,\text{[D110]}\,\right\rangle^{\!3}
\left\langle\,\text{[D111]}\,\right\rangle
&{}=v^4\left\langle\,\text{[D112]}\,\right\rangle^{\!3}
\left\langle\,\text{[D113]}\,\right\rangle.
\end{array}
```

 [D110](diagram-index.md#d110); [D111](diagram-index.md#d111); [D112](diagram-index.md#d112); [D113](diagram-index.md#d113)


For $m=2$ this is $v^4(v+v^{-1})^3(v^2+1+v^{-2})$, giving $2^3\cdot3=24$ at $v=1$. [Section 5](#sec-aggregate-calibration) expands and corrects this product.


<a id="section-4"></a>

## 4. The base change (main calculation)

<!-- Source: source.tex lines 4743; PDF page 19. -->


<a id="sec-algebraic-relevance"></a>


The following section is the main calculation, which is a bit tedious, though not difficult. The reader might want to skip to [Section 6](#sec-guralnick) for the conclusion, or to [Section 5](#sec-aggregate-calibration) for an example.


<a id="section-4a"></a>

### 4A. Parameters and degrees

<!-- Source: source.tex lines 4748; PDF page 19. -->


Degrees of flag counts restrict the canonical support to six families and the multiplicities of $A_{j;m}$ to zero or one.


<a id="def-relevance-parameters"></a>


**Definition 4A.1.** [Source](source.tex#L4753); [PDF p. 19](source.pdf#page=19).


Write $r=m-\ell$, with $0\le r\le m$. Every matrix in the support of [Proposition 3C.4](#prop-gallery-standard) has the form 

```latex
\begin{gather*}
A=\begin{pmatrix}
a&\ell+s-a&r-s\\
\beta&\delta-\beta&1-\delta\\
r-a-\beta&\ell+1-s-\delta+a+\beta&s+\delta-1
\end{pmatrix},\qquad a_{i+3,j+3}=a_{ij}.
\end{gather*}
```

 All entries are nonnegative. Thus $(\beta,\delta)\in\{(0,0),(0,1),(1,1)\}$, and $s\ge1$ if $\delta=0$. The intersection dimensions from [Definition 3C.1](#def-gallery-flags) are $b=a+\beta$, $c=\ell+s$ and $d=\ell+s+\delta$; put $z=s+\delta-1$.


<a id="lem-gallery-degrees"></a>


**Lemma 4A.2.** [Source](source.tex#L4769); [PDF p. 19](source.pdf#page=19).


For $q=Q=v^{-2}$ and $\ell\ge1$, the four flag counts give


<a id="eq-relevance-four-terms"></a>


```latex
\begin{gather}
\begin{aligned}
F_A(q)={}&[\ell]_q([\ell+b]_q-[z]_q)
\left([a]_q\genfrac{[}{]}{0pt}{}{2\ell}{\ell}_q+
([c]_q-[a]_q)\genfrac{[}{]}{0pt}{}{2\ell-1}{\ell-1}_q\right)\\
&+[\ell+1]_q[z]_q
\left([a]_q\genfrac{[}{]}{0pt}{}{2\ell+1}{\ell}_q+
([c]_q-[a]_q)\genfrac{[}{]}{0pt}{}{2\ell}{\ell-1}_q\right).
\end{aligned}
\end{gather}
```

 For $\ell=0$, $F_A(q)=[a]_q[d-1]_q$. Empty factors are zero. All summands are nonnegative. Define the length deficit 

```latex
\begin{gather*}
C=s(\ell+s)+a(\ell+a-s+1)+\beta(\ell+a+\beta)
+(\delta-\beta)(s+\delta-1).
\end{gather*}
```

 Then, with $D=2m^2+2m-3$, $d_A=2r(N-r)-C$, $D-d_A=2\ell(\ell+1)-3+C$.

**Proof.**

Substitute the intersection dimensions into [Equation 3C.2](#eq-gallery-gaussian). Since $c\ge a$ and $\ell+b\ge z$, the differences of quantum integers are nonnegative. In the length sum of [Definition 2E.2](#def-schur-bases), only two row periods contribute: the predecessor gives $r^2$, the product of the outer column sums, and the current period gives 

```latex
\sum_{1\le k\le i\le3}
\bigl(a_{i,-2}a_{k,1}+a_{i,-2}a_{k,4}+a_{i,1}a_{k,4}\bigr).
```

 Their sum is $2r(r+2\ell+1)-C$, giving both length identities.

*End of proof.*


<a id="section-4b"></a>

### 4B. A bound from positivity

<!-- Source: source.tex lines 4805; PDF page 19. -->


Write $\operatorname{val}$ and $\deg$ for the least and greatest exponents of a nonzero Laurent polynomial. We apply positivity to $d_m\mathcal R_m=M_eC_JC_KC_V$, not to the quotient itself.


<a id="lem-undivided-positivity-degree"></a>


**Lemma 4B.1.** [Source](source.tex#L4811); [PDF p. 19](source.pdf#page=19).


Let $R=\sum_S f_S[S]_v=\sum_S g_SC_S$ be integral and bar invariant. Suppose $d(v)$ is nonzero, positive and bar symmetric, and all canonical coefficients of $dR$ are nonnegative. If $g_S\ne0$, then 

```latex
\operatorname{val}g_S\ge\operatorname{val}f_S,\qquad
\deg g_S\le-\operatorname{val}f_S.
```

 Thus $\operatorname{val}f_S>0$ excludes $C_S$, and $\operatorname{val}f_S=0$ makes $g_S$ a nonnegative integer.

**Proof.**

Write $C_T=\sum_S h_{S,T}[S]_v$. These coefficients are nonnegative, with $h_{S,S}=1$ and $h_{S,T}\in v\mathbb Z[v]$ for $S<T$. Hence 

```latex
df_S=dg_S+\sum_{T>S}(dg_T)h_{S,T}
```

 is a sum of nonnegative polynomials, so $\operatorname{val}(dg_S)\ge\operatorname{val}(df_S)$. Cancel $\operatorname{val}d$ and use $g_S(v)=g_S(v^{-1})$. If $g_S$ is constant, positivity of $dg_S$ makes it nonnegative.

*End of proof.*

For $\mathcal R_m=\sum_A M_A(v)C_A$, integrality and bar invariance give $M_A\in\mathbb Z[v,v^{-1}]$ and $M_A(v)=M_A(v^{-1})$. Moreover, $d_mM_A\in\mathbb N[v,v^{-1}]$: the cleared product embeds as $C_{W_0}C_JC_KC_V$, whose KL coefficients and structure constants are positive [[KL80](#bib-kl80), [Spr82](#bib-springer82)]. The embedding preserves canonical normalization: for a minimal left-coset representative $x$, $C_{W_0}H_x$ has leading term $H_{w_{W_0}x}$, so its bar invariant triangular correction is $C_{w_{W_0}x}$. Grouping right $V$-cosets keeps leading coefficient one.

[Lemma 4B.1](#lem-undivided-positivity-degree) and [Proposition 3C.4](#prop-gallery-standard) now give


<a id="eq-relevance-bound"></a>


```latex
\begin{gather}
\operatorname{val}M_A\ge D-d_A-2\deg F_A,\quad
\deg M_A\le E_A:=2\deg F_A-(D-d_A)
\quad\text{whenever }M_A\ne0.
\end{gather}
```

 The same positive identity excludes every index whose standard coefficient vanishes.


<a id="section-4c"></a>

### 4C. The six families

<!-- Source: source.tex lines 4856; PDF page 20. -->


Families $\mathrm A$--$\mathrm F$ record the surviving web incidences; the labels are unrelated to Dynkin types.


<a id="def-six-families"></a>


**Definition 4C.1.** [Source](source.tex#L4861); [PDF p. 20](source.pdf#page=20).


Family $\mathrm A$ consists of the full-spherical elements: an endomorphism of $(N)$ followed by the ordinary split to $(m,1,m)$. Its rank $r$ index is 

```latex
Z_r=\begin{pmatrix}0&\ell&r\\0&1&0\\r&\ell&0\end{pmatrix},
\qquad\ell=m-r.
```

 Families $\mathrm E,\mathrm D$ retain one line, ending at cuts $m,m+1$ respectively; call them strong and weak. Their duals $\mathrm C,\mathrm B$ impose the hyperplane incidence. The operation $\vee$ reflects left--right, exchanges the outer edges and reverses winding. Family $\mathrm F$ imposes both incidences and consists of the desired $A_{r;m}$.

The six constructions appear below, with only the first splits labeled in the auxiliary panels. By the above, the four one-line webs become canonical after output refinement; family $\mathrm A$ uses $\mathcal V_r-\mathcal V_{r-1}$, while $\mathrm F$ contains all desired canonical elements.


```latex
\begin{gather*}
\begin{array}{@{}c@{\qquad}c@{\qquad}c@{}}
\mathrm A:\ \mathcal V_r&\mathrm B:\ \mathcal E_{r,m+1}^{\vee}
&\mathrm C:\ \mathcal E_{r,m}^{\vee}\\[.6ex]
\text{[D114]}&\text{[D115]}&\text{[D116]}\\[1.2ex]
\mathrm D:\ \mathcal E_{r,m+1}&\mathrm E:\ \mathcal E_{r,m}
&\mathrm F:\ \mathcal R_m\\[.6ex]
\text{[D117]}&\text{[D118]}&\text{[D119]}
\end{array}
\end{gather*}
```

 [D114](diagram-index.md#d114); [D115](diagram-index.md#d115); [D116](diagram-index.md#d116); [D117](diagram-index.md#d117); [D118](diagram-index.md#d118); [D119](diagram-index.md#d119)


<a id="prop-algebraic-six"></a>


**Lemma 4C.2.** [Source](source.tex#L4895); [PDF p. 20](source.pdf#page=20).


For $\ell\ge1$, only the following six families can occur in $\mathcal R_m=\sum_A M_A(v)C_A$. Discard infeasible positions and those with $E<0$. Every exponent of a nonzero $M_A$ lies in $[-E,E]$. 

```latex
\begin{array}{c|c|c|c|c}
\text{family}&(a,b,c,d)&C&\deg F_A&E=2\deg F_A-(D-d_A)\\\hline
\mathrm A&(0,0,\ell,\ell+1)&0&\ell^2+2\ell-3&2\ell-3\\
\mathrm B&(0,0,\ell+1,\ell+1)&\ell+1&\ell^2+2\ell-2&\ell-2\\
\mathrm C&(0,0,\ell+1,\ell+2)&\ell+2&\ell^2+2\ell-1&\ell-1\\
\mathrm D&(0,1,\ell,\ell+1)&\ell+1&\ell^2+2\ell-2&\ell-2\\
\mathrm E&(1,1,\ell,\ell+1)&\ell+2&\ell^2+2\ell-1&\ell-1\\
\mathrm F&(1,1,\ell+1,\ell+2)&2\ell+3&\ell^2+2\ell&0
\end{array}
```

 At $\ell=0$, only the index of $A_{m;m}$ can occur. For every feasible family $\mathrm F$ index, including $A_{m;m}$, $M_A\in\{0,1\}$; these indices are exactly $A_{r;m}$, $1\le r\le m$.

**Proof.**

Put $f_0=\ell^2+2\ell-3$. The four nonempty terms of [Equation 4A.3](#eq-relevance-four-terms) have degrees $f_0$ plus $2a+\beta$, $a+s+\beta$, $a+s+\delta$, $2s+\delta-1$. By [Equation 4B.2](#eq-relevance-bound), their maximum must give $E\ge0$. There are three possible middle rows.

*Middle row $(0,1,0)$: $(\beta,\delta)=(0,1)$.* Here the largest increment is at most $2\max(a,s)$, except when $a=s\ge1$, when it is at most $2a+1$. At $a=s=0$ the third term is empty. With $M=\max(a,s)$ and $u=\min(a,s)$, this bounds $E$ by 

```latex
(2-M-u)\ell-M^2-u^2+Mu+3M-u-3
+2\mathbf1_{M=u\ge1}.
```

 At $M=2$, $u=0,1$ give $-1,-\ell-1$; on $M=u\ge2$ the bound is $-2(u-1)\ell-(u-1)^2$. It decreases with $M$, losing the extra $2$ off the diagonal. Thus $M\ge2$ is impossible, leaving $a,s\in\{0,1\}$ and families $\mathrm A,C,E,F$.

*Middle row $(0,0,1)$: $(\beta,\delta)=(0,0)$.* Here we have $s\ge1$ and the largest increment is at most $\max(2a,2s-1)$. If $a\ge s$, then $E\le(2-a-s)\ell-a^2-s^2+as+3a-3$. At $a=s$ the right side is $(2-2s)\ell-s^2+3s-3<0$, and it decreases as $a$ increases. If $s\ge a+1$, then $E\le(2-a-s)\ell-a^2-s^2+as+4s-a-5$. For $a=0,s\ge2$ it starts at $-1$ and decreases; for $a\ge1$, it starts at $(1-2a)\ell-(a-1)^2-1<0$ when $s=a+1$ and decreases. Only $a=0,s=1$ remains: family $\mathrm B$.

*Middle row $(1,0,0)$: $(\beta,\delta)=(1,1)$.* Here the largest increment is at most $\max(2a+1,2s)$. If $a\ge s$, then $E\le(1-a-s)\ell-a^2-s^2+as+2a-2$. At $s=0,a=1$ it is $-1$; at $a=s\ge1$ it is $(1-2a)\ell-(a-1)^2-1$. Both decrease with $a$. If $s\ge a+1$, $E\le(1-a-s)\ell-a^2-s^2+as-2a+4s-4$. At $a=0,s=1$ it is $-1$. For $a\ge1,s=a+1$ it is $-2a\ell-a^2+a-1<0$. Increasing $s$ decreases it. Only $a=s=0$ remains, giving family $\mathrm D$. Substituting these six positions into the nonempty terms gives the displayed degrees exactly.

*The boundary case $\ell=0$.* A nonzero coefficient has $a\ge1$ and $d\ge2$, and $\deg F_A=a+d-3$. Feasibility forces $s=a$ in case $(0,1)$, and $s\in\{a,a+1\}$ in the other two cases. The respective values of $E$ are 

```latex
\begin{array}{c|cc}
(\beta,\delta)&s=a&s=a+1\\\hline
(0,1)&-(a-1)^2&\text{infeasible}\\
(0,0)&-a^2+3a-3&-(a-1)^2-1\\
(1,1)&-(a-1)^2-1&-a^2+a-1.
\end{array}
```

 Only $a=s=1$, $(\beta,\delta)=(0,1)$ has nonnegative excess.

In family $\mathrm F$, the unique top-degree term is $[\ell+1]_q\genfrac{[}{]}{0pt}{}{2\ell+1}{\ell}_q$, monic; at $\ell=0$, $F_A=1$. Hence $[\Delta_A]\mathcal R_m$ has valuation zero and constant one, so $M_A$ is constant. Since $d_mM_A$ is nonnegative and $d_m$ has lowest coefficient one, the positive identity above [Equation 4B.2](#eq-relevance-bound) gives $0\le M_A\le1$. The family $\mathrm F$ matrix is 

```latex
\begin{pmatrix}1&m-r&r-1\\0&1&0\\r-1&m-r&1\end{pmatrix},
```

 which is $A_{r;m}$. At $r=m$ its uncorrected leading coefficient is one and it is the unique maximal standard index, so in fact $M_{A_{m;m}}=1$.

*End of proof.*


<a id="section-4d"></a>

### 4D. Output refinement

<!-- Source: source.tex lines 4985; PDF page 21. -->


We have the following lemma.


<a id="lem-output-refinement"></a>


**Lemma 4D.1.** [Source](source.tex#L4989); [PDF p. 21](source.pdf#page=21).


For finite output parabolics $P\subset T$, partition a coarse double coset $D$ into fine double cosets $E$. Then


<a id="eq-parabolic-refinement"></a>


```latex
\begin{gather}
\Delta_D^T=\sum_{E\subset D}
v^{\ell(w_D^+)-\ell(w_E^+)}\Delta_E^P.
\end{gather}
```

 Refinement preserves $C_{w_Z^+}$ and, for $E\subset D$, $h^P_{E,Z}=v^{\ell(w_D^+)-\ell(w_E^+)}h^T_{D,Z}$. At the origin $Z_0$, the only fine coset is $B$ and the factor is one, so the distinguished coefficient is unchanged.

**Proof.**

Partition the unnormalized $T$-sum and compare normalization factors. Refinement leaves the underlying Hecke vector unchanged. At $Z_0$, both longest representatives are $w_0$.

*End of proof.*


<a id="section-4e"></a>

### 4E. No retained line

<!-- Source: source.tex lines 5008; PDF page 21. -->


<a id="sec-full-spherical-gallery"></a>


Next, we need the following.


<a id="def-spherical-web"></a>


**Definition 4E.1.** [Source](source.tex#L5012); [PDF p. 21](source.pdf#page=21).


For arbitrary $N$ and $0\le s\le\lfloor N/2\rfloor$, put $J_s=\langle s_i:i\ne s\rangle\cong S_N$ and $I_s=W_0\cap J_s\cong S_s\times S_{N-s}$. Define 

```latex
\mathcal V_s=\frac{M_eC_{J_s}C_{W_0}}{h_{I_s}^2},\qquad
\mathcal V_0=M_e.
```

 The web splits $(N)$ into $(s,N-s)$, merges and splits across the cut, then merges ordinarily. The spherical standard $Z_r$ has $r$ exponents of each sign and $N-2r$ zeros, with length gap $2r(N-r)$. We keep the notation after output refinement.

Matching $\alpha,\beta$ across the cuts gives 

```latex
\begin{gather*}
\mathcal V_s=\text{[D120]}
\quad\xleftrightarrow{\text{cut / glue}}\quad\text{[D121]}.
\end{gather*}
```

 [D120](diagram-index.md#d120); [D121](diagram-index.md#d121)

 For $\mathcal V_2:(5)\to(5)$, the annular stages are 

```latex
\begin{gather*}
\begin{array}{c@{\quad}c@{\quad}c@{\quad}c}
\text{(a) Split }(2,3)&\text{(b) Annular merge}&
\text{(c) Annular split}&\text{(d) Merge}\\[.6ex]
\text{[D122]}&\text{[D123]}&
\text{[D124]}&\text{[D125]}
\end{array}
\end{gather*}
```

 [D122](diagram-index.md#d122); [D123](diagram-index.md#d123); [D124](diagram-index.md#d124); [D125](diagram-index.md#d125)

 All inner inputs have label $5$; (b) merges the entire edge.


<a id="prop-full-gaussian-algebraic"></a>


**Lemma 4E.2.** [Source](source.tex#L5042); [PDF p. 22](source.pdf#page=22).


The standard coefficient of $\mathcal V_s$ at $Z_r$ is zero for $r>s$, and for $0\le r\le s$ equals


<a id="eq-full-raw-coefficient"></a>


```latex
\begin{gather}
v^{2s(N-s)-2r(N-r)}
\genfrac{[}{]}{0pt}{}{N-2r}{s-r}_{v^{-2}}.
\end{gather}
```

 Moreover, in the canonical basis, $\mathcal V_s=\sum_{a=0}^s C_{Z_a}$.

**Proof.**

The gallery chooses a type-$s$ lattice $\widetilde U$ between the fixed vertices: 

```latex
\Lambda+\Lambda'\subset\widetilde U
\subset t^{-1}\Lambda\cap t^{-1}\Lambda',
\qquad \dim(\widetilde U/\Lambda)=s.
```

 At rank $r$, this chooses an $(s-r)$-space in dimension $N-2r$, giving the Gaussian. Normalization gives $2(\ell(w_0)-\ell(w_{I_s}))-2r(N-r)
=2s(N-s)-2r(N-r)$. Thus the expression is integral and bar invariant.

Apply [Lemma 4B.1](#lem-undivided-positivity-degree) with $d=h_{I_s}^2$; clearing $d$ gives a positive product of canonical symmetrizers. The standard coefficients have valuation zero and constant one, so the degree bound and bar symmetry make all multiplicities constant. Descending through ranks, larger canonical terms have positive degree at smaller standards. The constant term therefore gives each multiplicity as one.

*End of proof.*

Put $h=s-r$ and $n=N-2r$. Since $2s(N-s)-2r(N-r)=2h(n-h)$, the coefficient is

$\displaystyle
\big[[Z_r]_v\big]\mathcal V_s
=v^{h(n-h)}\left\langle\,\text{[D126]}\,\right\rangle.$ [D126](diagram-index.md#d126)

The digon has extreme degrees $\pm h(n-h)$ with coefficients one, hence valuation zero and constant one after shifting.


<a id="cor-spherical-differences"></a>


**Lemma 4E.4.** [Source](source.tex#L5089); [PDF p. 22](source.pdf#page=22).


The spherical canonical elements are 

```latex
C_{Z_0}=\mathcal V_0=M_e,\qquad
C_{Z_s}=\mathcal V_s-\mathcal V_{s-1}\quad(s\ge1).
```

 For $0\le r\le s$, put $n=N-2r$, $h=s-r$, and $Q=v^{-2}$. Then


<a id="eq-full-canonical-coefficient"></a>


```latex
\begin{gather}
\big[[Z_r]_v\big]C_{Z_s}
=v^{2s(N-s)-2r(N-r)}
\left(\genfrac{[}{]}{0pt}{}{n}{h}_Q-Q^{n-2h+1}\genfrac{[}{]}{0pt}{}{n}{h-1}_Q\right).
\end{gather}
```


**Proof.**

Subtract the canonical expansions in [Lemma 4E.2](#prop-full-gaussian-algebraic), then the coefficients in [Equation 4E.3](#eq-full-raw-coefficient). Their normalization exponents differ by $2(N-2s+1)=2(n-2h+1)$, giving the power of $Q$. The case $s=0$ is immediate.

*End of proof.*

Write $K_{\alpha,\beta}(t)$ for the Kostka--Foulkes transition polynomial from Schur to Hall--Littlewood functions. Gaussian reciprocity with $t=v^2$ rewrites [Equation 4E.5](#eq-full-canonical-coefficient) as 

```latex
\big[[Z_r]_v\big]C_{Z_s}
=\genfrac{[}{]}{0pt}{}{n}{h}_t-\genfrac{[}{]}{0pt}{}{n}{h-1}_t
=K_{(2^h,1^{n-2h}),(1^n)}(t).
```

 Here a Gaussian with lower index $-1$ is zero. The last equality is the two-column case of Macdonald's hook formula [[Mac95](#bib-macdonald), Chapter~III, Section~6, Example~2]. This spherical affine KL interpretation goes back to Lusztig [[Lus83](#bib-lusztigspherical)] and Kato [[Kat82](#bib-kato)]; [[NR03](#bib-nelsenram), Theorem~3.4(d)] gives an explicit account of the inverse parameter convention. This gives the full-spherical correction in our three-output calculation. In the web calculus, for $h\ge1$ the same coordinate is 

```latex
[[Z_r]_v]C_{Z_s}
=v^{h(n-h)}\left\langle\,\text{[D127]}\,\right\rangle
-v^{(h-1)(n-h+1)}\left\langle\,\text{[D128]}\,\right\rangle.
```

 [D127](diagram-index.md#d127); [D128](diagram-index.md#d128)

 This is an identity of scalar coordinates: remove each digon, then take the difference. At $h=1$ the second web is the straight $n$-strand, and at $h=0$ the coordinate is one.

For $N=5$, cut open and on the annulus, these differences are 

```latex
\begin{gather*}
\begin{array}{c@{\qquad}c}
C_{Z_1}=\text{[D129]}-\text{[D130]}&
C_{Z_2}=\text{[D131]}-\text{[D132]}
\end{array}\displaybreak[1]\\[.5ex]
\begin{array}{c@{\quad}c}
C_{Z_1}=\text{[D133]}-\text{[D134]}&
C_{Z_2}=\text{[D135]}-\text{[D136]}
\end{array}
\end{gather*}
```

 [D129](diagram-index.md#d129); [D130](diagram-index.md#d130); [D131](diagram-index.md#d131); [D132](diagram-index.md#d132); [D133](diagram-index.md#d133); [D134](diagram-index.md#d134); [D135](diagram-index.md#d135); [D136](diagram-index.md#d136)

 Here $\mathcal V_0$ is the identity; the first splits are $(1,4)$ and $(2,3)$.

At $N=5$, the coefficients at the origin are 

```latex
\begin{array}{c|c|c}
\text{web}&[[Z_0]_v]\text{web}&\text{canonical difference at }Z_0\\\hline
\mathcal V_0&1&1\\
\mathcal V_1&1+v^2+v^4+v^6+v^8&v^2+v^4+v^6+v^8\\
\mathcal V_2&1+v^2+2v^4+2v^6+2v^8+v^{10}+v^{12}
&v^4+v^6+v^8+v^{10}+v^{12}
\end{array}
```


<a id="eq-refined-spherical-picture"></a>


```latex
\begin{gather}
\begin{minipage}[c]{.23\linewidth}
\raggedright
Appending the splitter of [Equation 2E.9](#fig-spherical-boundary) gives
\end{minipage}\qquad
C_{Z_r}=\text{[D137]}-\text{[D138]}
\qquad(r\ge1).
\end{gather}
```

 [D137](diagram-index.md#d137); [D138](diagram-index.md#d138)

 At rank zero the refined canonical web is the ordinary splitter $B_m$.


<a id="section-4f"></a>

### 4F. One retained line

<!-- Source: source.tex lines 5169; PDF page 24. -->


We need the following.


<a id="def-one-line-web"></a>


**Definition 4F.1.** [Source](source.tex#L5173); [PDF p. 24](source.pdf#page=24).


Let $j\ge1$, $N\ge2j+1$ and $j\le f\le N-j$, and put 

```latex
J_j=\langle s_i:i\ne j\rangle,\quad
K_1=\langle s_2,\ldots,s_{N-1}\rangle,\quad
T_f=\langle s_i:1\le i<N,\ i\ne f\rangle.
```

 The web below represents $\mathcal E_{j,f}:(N)\to(f,N-f)$, defined by 

```latex
\begin{gather*}
\mathcal E_{j,f}=
\frac{M_eC_{J_j}C_{K_1}C_{T_f}}
{[j]![N-j]!\,[j-1]![N-j]!\,[f-1]![N-f]!}.
\end{gather*}
```


The web and its middle stage are 

```latex
\begin{gather*}
\mathcal E_{j,f}=\text{[D139]}
\qquad\text{with middle stage}\qquad\text{[D140]}.
\end{gather*}
```

 [D139](diagram-index.md#d139); [D140](diagram-index.md#d140)

 At $j=1$ or $f=1$, delete the zero edge and its identity vertex. For $\mathcal E_{2,3}:(7)\to(3,4)$, the annular stages are 

```latex
\begin{gather*}
\begin{array}{c@{\quad}c@{\quad}c@{\quad}c}
\text{(a) Split }(2,5)&\text{(b) Annular merge}&
\text{(c) Retain one line}&\text{(d) Split and rejoin}\\[.6ex]
\text{[D141]}&\text{[D142]}&
\text{[D143]}&\text{[D144]}
\end{array}
\end{gather*}
```

 [D141](diagram-index.md#d141); [D142](diagram-index.md#d142); [D143](diagram-index.md#d143); [D144](diagram-index.md#d144)

 At (c) the output is $(1,6)$; at (d) split the $6$ into $(2,4)$ and join the blue line to the $2$-edge.

For a rank $r$ standard, set $n=N-2r$, $s=j-r$, $d=f-r$. Its intersection dimensions $a=\dim(I_0\cap F)$ and $c=\dim(K_0\cap F)=d+b$ give the nonnegative matrix 

```latex
Z=\begin{pmatrix}
a&d+b-a&r-b\\r-a&n-d-b+a&b
\end{pmatrix}.
```

 The length deficit and normalization exponent are 

```latex
C=b(d+b)+a(n-d+a-b),\qquad d_Z=2r(N-r)-C,\qquad
E=(2j-1)(N-j)+f-1.
```


<a id="prop-one-mark-canonical"></a>


**Lemma 4F.2.** [Source](source.tex#L5220); [PDF p. 24](source.pdf#page=24).


The coefficient of the normalized standard $Z$ in $\mathcal E_{j,f}$ is


<a id="eq-one-mark-coefficient"></a>


```latex
\begin{gather}
v^{E-d_Z}\left(
[a]_Q\genfrac{[}{]}{0pt}{}{n}{s}_Q+
([c]_Q-[a]_Q)\genfrac{[}{]}{0pt}{}{n-1}{s-1}_Q\right),\qquad Q=v^{-2}.
\end{gather}
```

 All other coefficients vanish. The web is a canonical basis element. In particular its coefficient at $B$ is $[[B]_v]\mathcal E_{j,f}
=v^E[f]_Q\genfrac{[}{]}{0pt}{}{N-1}{j-1}_Q$.

**Proof.**

A gallery chooses a type-$j$ lattice $\widetilde U$, a target vertex, a line $L\subset\widetilde U/\Lambda'$, and the prescribed $f$-space $F$ containing $L$. In the finite quotient, these choices are 

```latex
L\subset F\cap K_0,\qquad
I_0+L\subset U\subset K_0,\qquad \dim U=j.
```

 The $[a]_Q$ lines in $I_0$ allow $\genfrac{[}{]}{0pt}{}{n}{s}_Q$ choices of $U$; the other $[c]_Q-[a]_Q$ lines allow $\genfrac{[}{]}{0pt}{}{n-1}{s-1}_Q$. Successive parabolic intersections are $S_j\times S_{N-j}$, $S_{j-1}\times S_{N-j}$, and $S_{f-1}\times S_{N-f}$. Their Poincaré factors give the denominator, and subtracting their longest lengths from the numerator lengths gives $E$. This proves the integral coefficient formula; the symmetrizer expression is bar invariant.

For canonicality, the length gap and the degrees of the two nonzero polynomial pieces are 

```latex
\begin{gather*}
E-d_Z=2s(n-s)-(n-d-s+1)+C,\\
f_1=a-1+s(n-s),\qquad f_2=c-1+(s-1)(n-s).
\shortintertext{Subtracting gives}
\begin{aligned}
2f_1-(E-d_Z)
&=-(a-1)(n-d+a-1)+b(a-d-b)-s,\\
2f_2-(E-d_Z)
&=-(n-d)+s-1+b(2-d-b)-a(n-d+a-b).
\end{aligned}
\end{gather*}
```

 For the first piece $a\ge1$, $n-d\ge s$, and $a\le d+b$. Its bound is nonpositive, with equality only at $s=0,a=1,b=0$ when $d\ge1$, or $s=0,a=b=1$ when $d=0$. These give one leading standard, with coefficient one. For the second piece, if $d\ge1$ then $b(2-d-b)\le0$, so the bound is at most $-1$. If $d=0$, the hypotheses force $r=j=f$ and $s=0$, while $n\ge1$; since $b(2-b)\le1$, the bound is at most $-n<0$. Thus every proper standard coefficient lies in $v\mathbb Z[v]$. Any other Bruhat-maximal index would have a nonzero bar invariant coefficient in $v\mathbb Z[v]$, impossible. Thus the leading index is the unique maximum, proving canonicality.

*End of proof.*

For $N=5$, refine the output to $(2,1,2)$. The distinguished standard coefficient is unchanged by this refinement. At $B$, the normalization exponent is $E-(f-1)-(j-1)(N-j)=j(N-j)$. For $j=1$ the second digon is an identity, so the general formula and its first example are 

```latex
\begin{array}{c@{\qquad}c}
[[B]_v]\mathcal E_{j,f}&[[B_2]_v]\mathcal E_{1,2}\\[.4ex]
{}=v^{j(N-j)}\left\langle\,\text{[D145]}\,\right\rangle
\left\langle\,\text{[D146]}\,\right\rangle
&{}=v^4\left\langle\,\text{[D147]}\,\right\rangle=v^3+v^5.
\end{array}
```

 [D145](diagram-index.md#d145); [D146](diagram-index.md#d146); [D147](diagram-index.md#d147)

 Reflection gives the same coefficient for $\mathcal E_{1,2}^{\vee}$.


<a id="section-4g"></a>

### 4G. The refined family webs

<!-- Source: source.tex lines 5291; PDF page 25. -->


The strong and weak one-line refinements are 

```latex
\begin{gather*}
(m,m+1)\longrightarrow(m,1,m):\quad\text{[D148]},
\qquad
(m+1,m)\longrightarrow(m,1,m):\quad\text{[D149]}.
\end{gather*}
```

 [D148](diagram-index.md#d148); [D149](diagram-index.md#d149)


For $N=7$, $j=2$, split the right $4$-edge of $\mathcal E_{2,3}$ or the left $4$-edge of $\mathcal E_{2,4}$. Both retain the blue line and end at $(3,1,3)$:


```latex
\begin{gather*}
\begin{array}{c@{\qquad}c}
\text{[D150]}\circ\text{[D151]}=\text{[D152]}&
\text{[D153]}\circ\text{[D154]}=\text{[D155]}
\end{array}
\end{gather*}
```

 [D150](diagram-index.md#d150); [D151](diagram-index.md#d151); [D152](diagram-index.md#d152); [D153](diagram-index.md#d153); [D154](diagram-index.md#d154); [D155](diagram-index.md#d155)


<a id="section-4h"></a>

### 4H. The one-line degree bound

<!-- Source: source.tex lines 5312; PDF page 25. -->


Set $N=2m+1$. The image families have $f=m$ or $m+1$ for strong or weak incidence; reflection gives the kernel families. By [Equation 4D.2](#eq-parabolic-refinement), output refinement to $(m,1,m)$ preserves their canonical vectors.


<a id="cor-one-mark-margin"></a>


**Lemma 4H.1.** [Source](source.tex#L5319); [PDF p. 25](source.pdf#page=25).


Let a one-line canonical term have rank $s$, and put $l'=m-s$. At a full-spherical standard of rank $r<s$, its minimum degree is $l'+2$ for the strong family and $l'+1$ for the weak family. After multiplying by its coefficient in $\mathcal R_m$, the minimum degree is at least three in either case. The same holds for the dual families.

**Proof.**

At this standard $a=0,c=f-r$, so the polynomial in [Equation 4F.3](#eq-one-mark-coefficient) is $[f-r]_Q\genfrac{[}{]}{0pt}{}{N-2r-1}{s-r-1}_Q$. Subtracting twice its degree from the length gap gives $N-s-f+1$. The relevance bounds allow multiplicity degrees down to $-(l'-1)$ and $-(l'-2)$ respectively. Both resulting margins are three. For $s\le r$ the coefficient vanishes.

*End of proof.*

Diagrammatically, the margins are

$\displaystyle\begin{array}{c@{\qquad}c}
\text{[D156]}&\text{[D157]}\\[1ex]
\text{strong: }(l'+2)-(l'-1)=3&
\text{weak: }(l'+1)-(l'-2)=3
\end{array}$ [D156](diagram-index.md#d156); [D157](diagram-index.md#d157)

Reflection gives the other two cases.


<a id="section-4i"></a>

### 4I. Multiplicity one

<!-- Source: source.tex lines 5354; PDF page 26. -->


<a id="sec-multiplicity-one"></a>


We now control the multiplicity.


<a id="lem-all-two-mark-multiplicities"></a>


**Lemma 4I.1.** [Source](source.tex#L5358); [PDF p. 26](source.pdf#page=26).


Every family $\mathrm F$ index has multiplicity $M_{A_{j;m}}=1$ for $1\le j\le m$.

**Proof.**

Fix $j$ and an auxiliary rank $s\ge j$. Put $h=s-j$, $k=m-j$ and $\ell=m-s=k-h$. Full-spherical refinement to $A_{j;m}$ contributes the factor $v^{2k+3}$. Its canonical coefficient has nonnegative valuation and its multiplicity has valuation at least $-(2\ell-3)$, so the total valuation is at least $(2k+3)-(2\ell-3)=2h+6$.

For a strong one-line term (mark dimension $f=m$), the relative parameters in [Equation 4F.3](#eq-one-mark-coefficient) are $n=2k+1$, $a=b=1$, $c=k+1$, $d=k$. For the weak term ($f=m+1$), only $c,d$ change, to $k+2,k+1$. The codimension statistic for either two-row matrix is $2k+2$; refinement to the three-row matrix therefore adds one more power of $v$. Their counting polynomials are, respectively, 

```latex
\genfrac{[}{]}{0pt}{}{n}{h}_Q+([k+1]_Q-1)\genfrac{[}{]}{0pt}{}{n-1}{h-1}_Q,
\qquad
\genfrac{[}{]}{0pt}{}{n}{h}_Q+([k+2]_Q-1)\genfrac{[}{]}{0pt}{}{n-1}{h-1}_Q.
```

 The first Gaussian has degree $h(n-h)$. The second is lower by $\ell+1$ or $\ell$, respectively, and absent at $h=0$. Here $\ell\ge1$ by [Lemma 4C.2](#prop-algebraic-six). Subtracting twice the degree from the refined length gap gives valuations $\ell+2h+1$, $\ell+2h+2$. The multiplicity bounds $-(\ell-1)$, $-(\ell-2)$ leave total valuations at least $2h+2$, $2h+4$, respectively. Reflection gives the same bounds for the kernel families; the auxiliary canonical coefficients vanish at rank $j>s$.

The remaining terms $C_{A_{s;m}}$ have constant multiplicity zero or one. For $s>j$, their coefficients at $A_{j;m}$ lie in $v\mathbb Z[v]$ by strict triangularity; for $s<j$, their smaller length excludes them. Thus only $M_{A_{j;m}}C_{A_{j;m}}$ contributes to the constant one, proving $M_{A_{j;m}}=1$.

*End of proof.*


<a id="section-4j"></a>

### 4J. A Gaussian cancellation

<!-- Source: source.tex lines 5401; PDF page 26. -->


At a full-spherical standard of rank $r$, put $l=m-r$ and 

```latex
\begin{gathered}
D_l=2l(l+1)-3,\qquad e_l=(D_l-1)/2,\\
Y_l(q)=[l]_q^3\genfrac{[}{]}{0pt}{}{2l-1}{l-1}_q,\qquad
R_{n,h}(q)=\genfrac{[}{]}{0pt}{}{n}{h}_q-q^{n-2h+1}\genfrac{[}{]}{0pt}{}{n}{h-1}_q.
\end{gathered}
```

 To remove the nonpositive powers of $v$ from $v^{D_l}Y_l(v^{-2})$, we use the bar-symmetric polynomials 

```latex
\begin{gather*}
g_l(v)=\sum_{t=0}^{l-2}\binom{t+3}{3}
\left(v^{2l-3-2t}+v^{-(2l-3-2t)}\right)\quad(l\ge2),
\qquad g_1=0.
\end{gather*}
```

 For example, $g_2=v+v^{-1}$ and $g_3=v^3+4v+4v^{-1}+v^{-3}$. Write 

```latex
H_l(q)=\sum_{t=0}^{l-2}\binom{t+3}{3}
(q^t+q^{2l-3-t}),\qquad M_l(q)=q^{l^2}H_l(q),
\qquad H_1=M_1=0.
```

 Then $v^{D_l}M_l(v^{-2})=g_l(v)$. The coefficients $\binom{t+3}{3}$ are those of $(1-q)^{-4}$, whose truncation we use next.


<a id="lem-gaussian-truncation"></a>


**Lemma 4J.1.** [Source](source.tex#L5429); [PDF p. 26](source.pdf#page=26).


Fix $m\ge2$ and put $\Delta_r(q)=\genfrac{[}{]}{0pt}{}{2m+1}{r}_q-\genfrac{[}{]}{0pt}{}{2m+1}{r-1}_q$. As formal power series modulo $q^m$, 

```latex
\begin{align*}
q^rH_{m-r}(q)&\equiv\frac{q^r}{(1-q)^4}
-\binom{m-r+1}{2}q^{m-1}\qquad(0\le r\le m-1),\\
\sum_{r=0}^{m-1}q^r\Delta_r(q)&\equiv
\frac{1-q}{(q;q)_\infty},
\end{align*}
```

 where $(q;q)_r=\prod_{i=1}^r(1-q^i)$ and $(q;q)_\infty=\prod_{i\ge1}(1-q^i)$.

**Proof.**

Put $l=m-r$. The coefficients of $H_l$ agree with $(1-q)^{-4}$ through degree $l-2$. At degree $l-1$ the difference is $\binom{l+2}{3}-\binom{l+1}{3}=\binom{l+1}{2}$. This also gives the endpoint $l=1$, since $H_1=0$.

For the second identity, telescope the Gaussian differences: 

```latex
\sum_{r=0}^{m-1}q^r\Delta_r
\equiv(1-q)\sum_{r=0}^{m-1}q^r\genfrac{[}{]}{0pt}{}{2m+1}{r}_q
\equiv(1-q)\sum_{r\ge0}\frac{q^r}{(q;q)_r}
\pmod{q^m}.
```

 Here $\genfrac{[}{]}{0pt}{}{2m+1}{r}_q\equiv1/(q;q)_r\pmod{q^m}$ for $0\le r\le m-1$. Euler's partition identity $\sum_{r\ge0}q^r/(q;q)_r=1/(q;q)_\infty$ finishes the proof [[Mac95](#bib-macdonald), Chapter~I, Section~2, Example~4].

*End of proof.*


<a id="lem-gaussian-cancellation"></a>


**Lemma 4J.2.** [Source](source.tex#L5462); [PDF p. 27](source.pdf#page=27).


For every $m\ge2$, the polynomial 

```latex
\begin{gather*}
Q_m(q)=Y_m(q)-\sum_{r=0}^{m-2}M_{m-r}(q)R_{2m+1,r}(q)
\end{gather*}
```

 has degree at most $e_m$ and $[q^{e_m}]Q_m(q)=\binom{m+1}{2}$.

**Proof.**

The unwanted low powers of $v$ correspond to high powers of $q$, which we bring to degree zero by reversing the polynomials. Put $T=m^2+2m-3=\deg Y_m$. Gaussian reciprocity and reciprocity of $H_l$ give 

```latex
q^T(M_{m-r}R_{2m+1,r})(q^{-1})
=q^rH_{m-r}(q)\Delta_r(q).
```

 Every reversed term is a polynomial, and $Y_m$ is reciprocal. We compute the reversal of $Q_m$ modulo $q^m$. In [Lemma 4J.1](#lem-gaussian-truncation), $\Delta_0(0)=1$ and $\Delta_r(0)=0$ for $r>0$. Including the $H_1$, the lemma gives 

```latex
\sum_{r=0}^{m-1}q^rH_{m-r}\Delta_r
\equiv\frac{1}{(1-q)^3(q;q)_\infty}
-\binom{m+1}{2}q^{m-1}\pmod{q^m}.
```

 On the other hand, $Y_m\equiv((1-q)^3(q;q)_\infty)^{-1}\pmod{q^m}$. The common series cancels, leaving 

```latex
q^TQ_m(q^{-1})\equiv\binom{m+1}{2}q^{m-1}\pmod{q^m}.
```

 Consequently all terms of $Q_m$ above degree $T-(m-1)=e_m$ vanish, and the coefficient in that degree is $\binom{m+1}{2}$.

*End of proof.*


<a id="section-4k"></a>

### 4K. Removing the full-spherical terms

<!-- Source: source.tex lines 5500; PDF page 27. -->


Next up:


<a id="prop-full-correction"></a>


**Lemma 4K.1.** [Source](source.tex#L5504); [PDF p. 27](source.pdf#page=27).


The coefficient of $C_{Z_r}$ in $\mathcal R_m$ is $g_{m-r}(v)$ for $0\le r\le m-2$; no full-spherical term of rank $m-1$ occurs. The integral bar invariant web 

```latex
\begin{gather*}
\mathcal R_m^{\mathrm{crit}}
=\mathcal R_m-\sum_{r=0}^{m-2}g_{m-r}(v)C_{Z_r}
\end{gather*}
```

 has at $B$ valuation at least one and coefficient $\binom{m+1}{2}$ at $v$.

**Proof.**

Descend through the spherical ranks. At $Z_r$, put $l=m-r$. The raw coordinate is $v^{D_l}Y_l(v^{-2})$, and the coordinate of $C_{Z_{r+h}}$ is $v^{2h(2l+1-h)}R_{2l+1,h}(v^{-2})$. The one-line contributions have valuation at least three by [Lemma 4H.1](#cor-one-mark-margin). The family $\mathrm F$ multiplicities are constant, and their coefficients here are proper canonical coefficients, hence have positive degree. Thus only spherical terms affect the nonpositive part.

The classification excludes $l=1$. Suppose the multiplicities at larger ranks are known. Since $D_l-D_{l-h}=2h(2l+1-h)$, subtracting those terms and the proposed $g_lC_{Z_r}$ leaves, at $Z_r$, $v^{D_l}Q_l(v^{-2})\in v\mathbb Z[v]$ by [Lemma 4J.2](#lem-gaussian-cancellation). Hence $M_{Z_r}-g_l\in v\mathbb Z[v]$. This difference is bar invariant, so it is zero. At $r=0$, the same lemma gives valuation at least one and coefficient $\binom{m+1}{2}$ at $v$.

*End of proof.*

The correction is a linear combination of webs built from splits and merges. Telescoping $C_{Z_r}=\mathcal V_r-\mathcal V_{r-1}$, with the outputs refined and $g_1=0$, gives


```latex
\begin{gather*}
\mathcal R_m^{\rm crit}
=\text{[D158]}
-\bigl(g_m-g_{m-1}\bigr)\text{[D159]}
-\sum_{r=1}^{m-2}\bigl(g_{m-r}-g_{m-r-1}\bigr)\text{[D160]}.
\end{gather*}
```

 [D158](diagram-index.md#d158); [D159](diagram-index.md#d159); [D160](diagram-index.md#d160)


All terms have boundary $(N)\to(m,1,m)$; the sum is empty for $m=2$. Using [Equation 4E.6](#eq-refined-spherical-picture), the first corrections are 

```latex
\begin{gather*}
\begin{aligned}
\mathcal R_2^{\rm crit}&=\mathcal R_2-(v+v^{-1})C_{Z_0},\\
\mathcal R_3^{\rm crit}&=\mathcal R_3
-(v^3+4v+4v^{-1}+v^{-3})C_{Z_0}
-(v+v^{-1})C_{Z_1}.
\end{aligned}
\end{gather*}
```

 For $m=3$, substitute $C_{Z_0}=B_3$ and $C_{Z_1}=\mathcal V_1-B_3$, with outputs refined, and collect terms: 

```latex
\begin{gather*}
\mathcal R_3^{\rm crit}
=\text{[D161]}-\bigl(g_3(v)-g_2(v)\bigr)\text{[D162]}
-g_2(v)\,\text{[D163]}.
\end{gather*}
```

 [D161](diagram-index.md#d161); [D162](diagram-index.md#d162); [D163](diagram-index.md#d163)

 At the chosen standard coordinate, 

```latex
\begin{array}{c|ccc|c}
\text{term}&\mathcal R_3&g_3C_{Z_0}&g_2C_{Z_1}&\mathcal R_3^{\rm crit}\\\hline
[v]\,[[B_3]_v]&11&4&1&11-4-1=6.
\end{array}
```

 The spherical contribution $1$ in this table is itself a digon calculation: 

```latex
[v]\,g_2(v)\left(v^6\left\langle\,\text{[D164]}\,\right\rangle-1\right)
=[v]\,(v+v^{-1})(v^2+v^4+\cdots+v^{12})=1.
```

 [D164](diagram-index.md#d164)

 Thus $11-4-1=6$ is $\mu_{1;3}+\mu_{2;3}+\mu_{3;3}$, since the one-line terms start in degree three.

For $m=4$, the boundary is $(9)\to(4,1,4)$. Here the refined $C_{Z_1}=\mathcal V_1-B_4$ and $C_{Z_2}=\mathcal V_2-\mathcal V_1$ have bottom splits $(1,8)$ and $(2,7)$. Collecting terms gives


```latex
\begin{gather*}
\mathcal R_4^{\rm crit}
=\text{[D165]}-\bigl(g_4(v)-g_3(v)\bigr)\text{[D166]}
-\bigl(g_3(v)-g_2(v)\bigr)\text{[D167]}
-g_2(v)\,\text{[D168]}.
\end{gather*}
```

 [D165](diagram-index.md#d165); [D166](diagram-index.md#d166); [D167](diagram-index.md#d167); [D168](diagram-index.md#d168)


The coefficient of $v$ sums the four mu-coefficients: 

```latex
\begin{array}{c|rrrr|r}
\text{term}&\mathcal R_4&g_4C_{Z_0}&g_3C_{Z_1}&g_2C_{Z_2}&\mathcal R_4^{\rm crit}\\\hline
[v]\,\big[[B_4]_v\big]&25&10&5&0&25-10-5-0=10
\end{array}
```


<a id="section-4l"></a>

### 4L. The critical coefficient

<!-- Source: source.tex lines 5600; PDF page 28. -->


The following is our main result.


<a id="thm-aggregate-web"></a>


**Theorem 4L.1.** [Source](source.tex#L5604); [PDF p. 28](source.pdf#page=28).


For every $m\ge2$, the endpoints $w_0$ and $C_{j;m}$ satisfy


<a id="eq-aggregate-web-theorem"></a>


```latex
\begin{gather}
\boxed{\displaystyle
\sum_{j=1}^{m}\mu_{j;m}=\binom{m+1}{2}.}
\end{gather}
```

 In particular $\max_{1\le j\le m}\mu_{j;m}\ge\lceil(m+1)/2\rceil$.

**Proof.**

The six-family classification and the multiplicity-one lemma give 

```latex
\mathcal R_m^{\mathrm{crit}}
=\sum_{j=1}^{m}C_{A_{j;m}}
+\sum_{\text{one-line }S}M_S(v)C_S.
```

 The last sum has minimum degree at least three at $B$. Taking $[v]$ and using the canonical-to-standard dictionary gives [Equation 4L.2](#eq-aggregate-web-theorem). Its consequence follows by averaging and integrality.

*End of proof.*

The sum $S_m=\sum_j\mu_{j;m}=\binom{m+1}{2}$ also counts triples of nonnegative integers summing to $m-1$, so $S_m=[q^{m-1}](1-q)^{-3}$ and $S_m-S_{m-1}=m$ for $m\ge3$. Equivalently, $S_m=[T^{m+1}]_{0,2}$: a path from $0$ to $2$ in $m+1$ steps advances twice, and we choose those steps.

These states count the sum; they do not represent canonical summands or blue strands.

$\displaystyle
\text{[D169]}$ [D169](diagram-index.md#d169)


<a id="section-5"></a>

## 5. The first example in pictures

<!-- Source: source.tex lines 5656; PDF page 29. -->


<a id="sec-aggregate-calibration"></a>


For $m=2$, the boundary is $(5)\to(2,1,2)$ and the intermediate refinement is thin. Removing the four smaller canonical summands recovers $\mu_{2;2}=2$ from [[SX10](#bib-sx), Lemma~3.4].


<a id="section-5a"></a>

### 5A. Constructing and expanding the web

<!-- Source: source.tex lines 5662; PDF page 29. -->


The completed webs $\mathcal R_2:(5)\to(2,1,2)$ and $\mathcal R_3:(7)\to(3,1,3)$ appear in [Figure 3](#fig-intro-affine-construction); their interior labels are in [Equation 3A.1](#fig-continuous-m2). Here are all six stages for $m=2$. Each composite has input $5$; the blue strands bypass the middle merge and split, then rejoin at (f): 

```latex
\begin{gather*}
\begin{array}{c@{\quad}c@{\quad}c}
\text{(a) Split}&\text{(b) Annular merge}&\text{(c) Separate the unit strands}\\[.6ex]
\text{[D170]}&\text{[D171]}&\text{[D172]}
\end{array}\displaybreak[1]\\[1.3ex]
\begin{array}{c@{\quad}c@{\quad}c}
\text{(d) Merge the middle}&\text{(e) Split the middle}&\text{(f) Rejoin the outer edges}\\[.6ex]
\text{[D173]}&\text{[D174]}&\text{[D175]}
\end{array}
\end{gather*}
```

 [D170](diagram-index.md#d170); [D171](diagram-index.md#d171); [D172](diagram-index.md#d172); [D173](diagram-index.md#d173); [D174](diagram-index.md#d174); [D175](diagram-index.md#d175)


<a id="lem-seed-expansion"></a>


**Lemma 5A.1.** [Source](source.tex#L5681); [PDF p. 29](source.pdf#page=29).


The canonical expansion is


<a id="eq-seed-aggregate-identity"></a>


```latex
\begin{gather}
\mathcal R_2=
\theta_{A_{2;2}}+\theta_{A_{1;2}}
+\mathcal E_{1,2}+\mathcal E_{1,2}^{\vee}
+(v+v^{-1})\theta_{B_2}.
\end{gather}
```

 Here both one-line webs have their outputs refined to $(2,1,2)$.

**Proof.**

The classification leaves these five terms. The family multiplicities are one by [Lemma 4I.1](#lem-all-two-mark-multiplicities); the one-line multiplicities are constant with leading coefficient one. Finally, $g_2=v+v^{-1}$.

*End of proof.*

Each pair below shows one of the two one-line webs, cut open and on the annulus: 

```latex
\begin{gather*}
\begin{array}{@{}c@{\quad}c@{}}
\mathcal E_{1,2}&\mathcal E_{1,2}^{\vee}\\[.6ex]
\text{[D176]}\;\text{[D177]}&
\text{[D178]}\;\text{[D179]}
\end{array}
\end{gather*}
```

 [D176](diagram-index.md#d176); [D177](diagram-index.md#d177); [D178](diagram-index.md#d178); [D179](diagram-index.md#d179)


Removing the source term gives $\mathcal R_2^{\rm crit}=\mathcal R_2-(v+v^{-1})B_2$, as drawn in [Figure 5](#fig-intro-critical-correction). To isolate $\theta_{A_{2;2}}$, we also need the smaller family term.


<a id="section-5b"></a>

### 5B. The rank-one correction

<!-- Source: source.tex lines 5714; PDF page 30. -->


The smaller family element comes from three local maps $b_i=H_i+v$. For a spherical standard $M_w$ indexed by a minimal left $W_0$-coset representative, 

```latex
\begin{gather*}
M_wb_i=\begin{cases}
M_{ws_i}+vM_w,&ws_i\text{ is minimal and }\ell(ws_i)=\ell(w)+1,\\
M_{ws_i}+v^{-1}M_w,&ws_i\text{ is minimal and }\ell(ws_i)=\ell(w)-1,\\
(v+v^{-1})M_w,&ws_i\text{ is not minimal}.
\end{cases}
\end{gather*}
```

 The last case retains the symmetric input. The product at $0,4,1$ gives $\mathcal U_2\longleftrightarrow M_e b_0b_4b_1$, with $[M_e](M_eb_0b_4b_1)=v^3+2v+v^{-1}$.

To draw $\mathcal U_2$, split into five thin strands, apply $b_0$ across the cut, and merge the outer pairs. Matching $\alpha,\beta$ recovers the two branches of $b_0$; the final merges give $b_4b_1$ in the inverse module. Its only nonpositive standard term is $v^{-1}$ at the origin. Subtracting $(v+v^{-1})M_e$ leaves all proper coefficients in $v\mathbb Z[v]$, so bar invariance gives 

```latex
\begin{gather*}
\theta_{A_{1;2}}=M_e b_0b_4b_1-(v+v^{-1})M_e,
\qquad \big[[B_2]_v\big]\theta_{A_{1;2}}=v+v^3.
\end{gather*}
```

 

```latex
\begin{gather*}
\text{In pictures,}\qquad
\theta_{A_{1;2}}=\underbrace{\text{[D180]}}_{\mathcal U_2}
-(v+v^{-1})\text{[D181]}.
\end{gather*}
```

 [D180](diagram-index.md#d180); [D181](diagram-index.md#d181)


<a id="section-5c"></a>

### 5C. Reading the coefficient

<!-- Source: source.tex lines 5746; PDF page 30. -->


Substitution cancels the source terms in [Equation 5A.2](#eq-seed-aggregate-identity): $\theta_{A_{2;2}}=\mathcal R_2-\mathcal U_2
-\mathcal E_{1,2}-\mathcal E_{1,2}^{\vee}$. All four webs have boundary $(5)\to(2,1,2)$. The numbers underneath are their $[v]\,[[B_2]_v]$ coordinates:


```latex
\begin{gather*}
\theta_{A_{2;2}}=
\underbrace{\text{[D182]}}_{4}
-\underbrace{\text{[D183]}}_{2}
-\underbrace{\text{[D184]}}_{0}
-\underbrace{\text{[D185]}}_{0}.
\end{gather*}
```

 [D182](diagram-index.md#d182); [D183](diagram-index.md#d183); [D184](diagram-index.md#d184); [D185](diagram-index.md#d185)


Their $B_2$ coordinates are 

```latex
\begin{array}{c|l}
\text{web}&\text{coefficient of }[B_2]_v\\\hline
\mathcal R_2&v^{-1}+4v+7v^3+7v^5+4v^7+v^9\\
\mathcal U_2&v^{-1}+2v+v^3\\
\mathcal E_{1,2}&v^3+v^5\\
\mathcal E_{1,2}^{\vee}&v^3+v^5
\end{array}
```

 Subtracting the last three rows from the first yields 

```latex
\begin{gather*}
\big[[B_2]_v\big]\theta_{A_{2;2}}
=2v+4v^3+5v^5+4v^7+v^9.
\end{gather*}
```

 For $u_{2;2}=(-4,-1,3,7,10)$, the endpoint $C_{2;2}=u_{2;2}w_0$ has length gap nine. Thus $P_{w_0,C_{2;2}}(Q)=1+4Q+5Q^2+4Q^3+2Q^4$. One gets $\mu_{2;2}=4-2=2$; the smaller element has $\mu_{1;2}=1$.


<a id="section-6"></a>

## 6. Application to Guralnick's conjecture

<!-- Source: source.tex lines 5784; PDF page 31. -->


<a id="sec-guralnick"></a>


We now pass to highest weights and finite group cohomology. Algebraic group extensions and cohomology are taken among rational modules. The input $(N)$ gives $M_e\mapsto C_{w_0}$, so the lower endpoint corresponds to the trivial module.


<a id="section-6a"></a>

### 6A. The highest weights

<!-- Source: source.tex lines 5791; PDF page 31. -->


Fix $N=2m+1$ and let $k=\overline{\mathbb F}_p$, with $p>N$. Write $G=\mathrm{SL}_N(k)$ and let $\omega_1,\ldots,\omega_{N-1}$ be its fundamental weights. Put $\eta_i=\omega_i+\omega_{N-i}$ for $1\le i\le m$, and $\eta_0=0$. For $1\le j\le m$, set $c=m-j$ and define


<a id="eq-application-weight"></a>


```latex
\begin{gather}
\lambda_{j;m}(p)
=(c+2)\eta_{j-1}+(p-c-3)\eta_j+\eta_m.
\end{gather}
```

 Write $L(\lambda)$ for the simple rational $G$-module of highest weight $\lambda$.

In sum-zero coordinates, put $\rho_i=(N+1-2i)/2$. For integral sum-zero $\xi$, the translation $t_\xi$ has window $t_\xi(i)=i+N\xi_i$ and positive $p$-dot action $(t_\xi z)\mathbin{\cdot_p}\lambda
=z(\lambda+\rho)+p\xi-\rho,\quad z\in S_N$.


<a id="lem-application-weight"></a>


**Lemma 6A.2.** [Source](source.tex#L5811); [PDF p. 31](source.pdf#page=31).


The weight $\lambda_{j;m}(p)=u_{j;m}^{-1}\cdot_p0$ is nonzero, dominant, $p$-restricted, $p$-regular and in the root lattice, with sum-zero coordinates


<a id="eq-application-coordinates"></a>


```latex
\begin{gather}
\bigl(p^{\times(j-1)},\ p-c-2,\ 1^{\times c},\ 0,\
(-1)^{\times c},\ c+2-p,\ (-p)^{\times(j-1)}\bigr),
\end{gather}
```

 where an exponent $\times a$ means $a$ repetitions.

**Proof.**

Write $u=u_{j;m}$ and $b=u^{-1}$. The increasing window is $u(i)=z_i+Ns_i$, with $1\le z_i\le N$; thus $b$ has permutation part $z^{-1}$ and translation coordinates $-s_i$. Hence $(b\cdot_p0)_i=-ps_i+\rho_{z_i}-\rho_i=-ps_i+i-z_i$. The negative-shift residues are $(1,\ldots,j-1,m+2)$, the positive-shift residues are $(m,N-j+2,\ldots,N)$, both in increasing order, and the remaining shifts are zero. Substitution gives [Equation 6A.3](#eq-application-coordinates); adjacent differences give [Equation 6A.1](#eq-application-weight).

For $j<m$, the nonzero fundamental-weight coefficients $c+2$, $p-c-3$, $1$ lie in $[0,p-1]$; for $j=m$, the weight is $2\eta_{m-1}+(p-2)\eta_m$, again dominant and restricted. The nonzero integral sum-zero vector lies in the root lattice. Finally, $\lambda+\rho$ is congruent modulo $p$ to a permutation of $\rho$, whose coordinate differences have absolute value between $1$ and $N-1<p$. Thus $\lambda$ is $p$-regular.

*End of proof.*


<a id="section-6b"></a>

### 6B. The cohomology coefficient

<!-- Source: source.tex lines 5842; PDF page 31. -->


Henceforth assume $p\ge5(N-1)$ and Lusztig's character formula for the $p$-restricted weights of $G$. For fixed $N$, all sufficiently large primes satisfy both conditions [[AJS94](#bib-ajs)]; see [[Lüb20](#bib-luebeck), Theorem~3.1].


<a id="prop-application-transfer"></a>


**Lemma 6B.1.** [Source](source.tex#L5849); [PDF p. 31](source.pdf#page=31).


For these primes and every $1\le j\le m$, 

```latex
\begin{gather*}
\dim_k H^1\Big(G,L\big(\lambda_{j;m}(p)\big)\Big)
=\dim_k H^1\Big(\mathrm{SL}_N(\mathbb F_p),L\big(\lambda_{j;m}(p)\big)\Big)
=\mu_{j;m}.
\end{gather*}
```

 The restricted finite group module is nontrivial and absolutely irreducible.

**Proof.**

Since $u=u_{j;m}$ is right finite-minimal, $b=u^{-1}$ is left finite-minimal. By [Section 2](#sec-dictionary), its normalized spherical coefficient at $M_e$ is 

```latex
m_{e,b}(v)=v^{D_{j;m}}P_{w_0,w_0b}(v^{-2})
=v^{D_{j;m}}P_{w_0,C_{j;m}}(v^{-2})
=\big[[B_m]_v\big]\theta_{A_{j;m}}.
```

 Here $w_0b=C_{j;m}^{-1}$, and KL polynomials are invariant under simultaneous inversion. Thus $[v]m_{e,b}(v)=\mu_{j;m}$. Andersen's cohomological interpretation [[And86](#bib-andersen)], as in [[Lüb20](#bib-luebeck), Theorem~4.5], gives 

```latex
[v]m_{e,b}=\dim_k\operatorname{Ext}^1_{G}\big(k,L(b\cdot_p0)\big)
=\dim_k H^1\big(G,L(b\cdot_p0)\big).
```

 The dominant restricted hypothesis is [Lemma 6A.2](#lem-application-weight).

The Coxeter number is $N$, so Bendel--Nakano--Pillen comparison [[BNP01](#bib-bnp), Theorem~7.5], in the form [[Lüb20](#bib-luebeck), Theorem~4.6], applies for $p\ge5(N-1)$, cohomological bound $s=1$, base weight $\nu=0$ and field exponent $r=1$, giving the finite group equality. Steinberg's restricted-module theorem [[Ste63](#bib-steinberg), Theorems~1.3, 6.1 and 7.4] gives irreducibility on restriction; see also [[Lüb20](#bib-luebeck), Proposition~5.3]. The nonzero restricted weight gives nontriviality, and algebraic closure of $k$ gives absolute irreducibility.

*End of proof.*


<a id="section-6c"></a>

### 6C. Passage to the finite simple quotient

<!-- Source: source.tex lines 5890; PDF page 32. -->


We now wrap up.


<a id="lem-simple-quotient"></a>


**Lemma 6C.1.** [Source](source.tex#L5894); [PDF p. 32](source.pdf#page=32).


The restricted module $L(\lambda_{j;m}(p))$ descends to a faithful absolutely irreducible module $M_{j;m}(p)$ for $H=\mathrm{PSL}_N(\mathbb F_p)$, and 

```latex
H^1\big(H,M_{j;m}(p)\big)
\cong H^1\Big(\mathrm{SL}_N(\mathbb F_p),L\big(\lambda_{j;m}(p)\big)\Big).
```


**Proof.**

The root-lattice condition makes the algebraic center act trivially. The finite center has order $\gcd(N,p-1)$, prime to $p$, so averaging and inflation--restriction give the isomorphism. Descent preserves absolute irreducibility and nontriviality. Since $N\ge5$, the group $H$ is nonabelian simple; its nontrivial representation is therefore faithful.

*End of proof.*


<a id="cor-guralnick"></a>


**Corollary 6C.2.** [Source](source.tex#L5913); [PDF p. 32](source.pdf#page=32).


For each $m\ge2$ and every sufficiently large prime $p$, the group $H=\mathrm{PSL}_{2m+1}(\mathbb F_p)$ has the faithful absolutely irreducible modules $M_{j;m}(p)$ defined above, and 

```latex
\begin{gather*}
\sum_{j=1}^{m}\dim_k H^1\big(H,M_{j;m}(p)\big)=\binom{m+1}{2},
\qquad
\max_{1\le j\le m}\dim_k H^1\big(H,M_{j;m}(p)\big)
\ge\left\lceil\frac{m+1}{2}\right\rceil.
\end{gather*}
```

 Thus Guralnick's absolute boundedness conjecture is false.

**Proof.**

Transfer identifies the summands with $\mu_{j;m}$. Apply [Theorem 4L.1](#thm-aggregate-web), average and use integrality; the lower bound tends to infinity.

*End of proof.*

For $m=2$, the Dynkin coordinates are $(p-4,1,1,p-4)$ and $(2,p-2,p-2,2)$. Under the stated characteristic assumptions, the first cohomology dimension for $H=\mathrm{PSL}_5(\mathbb F_p)$ is read from the normalized standard expansion of the corrected web: 

```latex
\begin{gather*}
\dim_k H^1\big(H,M_{1;2}(p)\big)
=[v]\,\left[\,\text{[D186]}\,\right]\!\left(\text{[D187]}-(v+v^{-1})\text{[D188]}\right)
=[v](v+v^3)=1.
\end{gather*}
```

 [D186](diagram-index.md#d186); [D187](diagram-index.md#d187); [D188](diagram-index.md#d188)

 For $M_{2;2}(p)$, the four pictured terms in [Section 5](#sec-aggregate-calibration) give $4-2-0-0=2$. The passage from these web coordinates to cohomology uses [Lemma 6B.1](#prop-application-transfer) and [Lemma 6C.1](#lem-simple-quotient).

For fixed root systems, first cohomology in defining characteristic is bounded by Cline--Parshall--Scott [[CPS09](#bib-cps)], and first extensions by Parshall--Scott [[PS11](#bib-parshallscott)]. For cross characteristic see [[GT11](#bib-guralnicktiep), [GT20](#bib-guralnicktiepsectional)]; for quantitative bounds in growing rank see [[PS14](#bib-parkerstewart)]. The ranks in our construction grow. By contrast, the earlier value $469>63=\dim\mathrm{SL}_8$, independently checked by Scott and Sprowl shortly after the June 2012 AIM workshop, already sufficed for the Wall counterexamples discussed in the introduction [[G+12](#bib-aimwall), [Lüb20](#bib-luebeck)]. Varying the field alone need not increase first cohomology.


<a id="section-7"></a>

## 7. Methods and AI assistance

<!-- Source: source.tex lines 5958; PDF page 32. -->


We explain how we found the construction and how AI entered the picture. The route was rather less tidy than the proof, so this section is written in an anecdotal style.


<a id="section-7a"></a>

### 7A. Our previous work as a starting point

<!-- Source: source.tex lines 5962; PDF page 32. -->


One prejudice we have acquired over the years is that once things get bad, they tend to get as bad as they possibly can. We have encountered versions of this phenomenon in rather different settings, from the prevalence of torsion in intersection cohomology [[BT26](#bib-torsionproliferation)] to the failure of standard link invariants to distinguish large families of links [[K+25](#bib-linkdetection)]. Lübeck's computations [[Lüb20](#bib-luebeck)], with first cohomology dimensions already running into the millions, certainly encouraged that prejudice here. We found it hard to believe that an absolute bound was waiting somewhere beyond them.

This paper grew out of our earlier work [[G+26b](#bib-finite)], where we used planar $\mathfrak{sl}_3$ webs to construct $\mu$-coefficients growing exponentially with $n$ in the symmetric groups $\mathrm{Aut}(\{1,\dots,n\})$. The construction repeats a small piece of web and controls the correction needed to obtain a canonical basis element. A complicated family of permutations thus becomes a fairly simple family of pictures. We wondered whether the same way of thinking could settle Guralnick's conjecture. There was an extra difficulty: large extension dimensions between arbitrary simple modules do not automatically give large first cohomology. For that, one of the modules must be trivial.

So we boldly asked GPT Astra 6.0: "Use our $\mu$-paper to solve Guralnick's conjecture." It first searched the literature and came back with the familiar obstruction: first cohomology requires the lower endpoint to be $w_0$, so an arbitrary family of large $\mu$-coefficients is not enough. It pointed us to [[SX10](#bib-sx), Section~4, final remark], where Scott--Xi explicitly leave open whether the coefficients $\mu(w_0,w)$ corresponding to first cohomology can be unbounded. Quite right, but hardly news to us. The silly part was treating this as a reason to stop.

So we took a stick and gave it a poke: "Come on, you do not have to take the request literally. Use the ideas and change the construction if necessary." It then obliged. Unfortunately, we did not understand the answer, and we went back to thinking about what a solution ought to look like.


<a id="section-7b"></a>

### 7B. Put hexagons on an annulus

<!-- Source: source.tex lines 6008; PDF page 33. -->


The guiding idea was simple enough: $\text{affine}=\text{annular}$. Putting diagrams on an annulus to obtain affine versions of familiar algebras is an old theme, going back several decades; see [[HT27](#bib-ht), Section~1B] for some historical background. Since the coefficients relevant to first cohomology live in affine KL theory, we should try putting our webs on an annulus.

There was also a more specific picture in mind. The connection between tensor canonical bases and KL polynomials [[FKK98](#bib-fkk)] makes the difference between a web and a canonical basis element particularly relevant. KK [[KK99](#bib-kk99)] showed that the $\mathfrak{sl}_3$ web basis need not be dual canonical. Their "hexagon-in-hexagons" picture (a central hexagon surrounded by six others, see the right of [Figure 6](#fig-heawood)) is a memorable example of where the two bases start to disagree. Related hexagonal patterns supplied the growing webs in [[G+26b](#bib-finite)]. Hexagons seemed a good place to look for trouble.

When we tried wrapping these pictures around an annulus, they reminded us of the classical embedding of the Heawood graph on a torus. This graph has $14$ vertices and $21$ edges, and the embedding has seven hexagonal faces. It can itself be drawn as one hexagon surrounded by six others, with suitable boundary identifications; see [Figure 6](#fig-heawood).


<a id="fig-heawood"></a>


[D189: drawing](diagram-index.md#d189) **Figure caption.** The Heawood graph, drawn in the plane and on a torus. On the right, identify opposite three-edge boundary paths with matching letters and arrows. The dashed red curves mark these pairings. The quotient has 14 vertices, 21 edges and seven hexagonal faces.

Cutting the torus open along a suitable noncontractible curve gives an annulus, with the cut edges ending on its boundary. The Heawood graph therefore looked like a rather tempting starting point: a tiny graph built from exactly the sort of hexagons we were looking for. We tried to turn this picture into a family of annular webs and work out the relevant $\mu$-coefficients. It did not quite work, but the picture still looked promising.


<a id="section-7c"></a>

### 7C. A little help with the graph

<!-- Source: source.tex lines 6119; PDF page 33. -->


In the earlier planar calculation, AI assistance had helped us modify an initial web family and find a canonical correction that worked uniformly [[G+26b](#bib-finite), Section~9]. That suggested trying the same division of labor here. We gave GPT Astra 6.0 the picture and asked it to make the idea work: massage the graph a little if necessary, and try to find a counterexample to Guralnick's conjecture.

It succeeded fairly quickly. The construction seems to generalize one of Scott--Xi's examples [[SX10](#bib-sx)], and looks rather natural when drawn on an annulus. This time we could understand the proof: the picture helped us see what the formulas were doing. The writing, however, was terrible. We took the argument as a blueprint and worked it into the present paper.

The resulting graph is not the Heawood graph, although its toroidal closure still has $14$ vertices and $21$ edges; compare [Figure 1](#fig-toroidal-closure). The particularly pleasant surprise is that the graph itself need not grow. In the planar construction we repeated web pieces; here we keep the graph and change only the edge thicknesses. This is enough to produce unbounded first cohomology.

<a id="ai-statement-057"></a>


**Remark 7C.1.** [Source](source.tex#L6147); [PDF p. 34](source.pdf#page=34).


The resemblance to the Heawood graph is rather concrete: our toroidal closure is just six Whitehead H=I moves away from its standard torus embedding; see [Figure 7](#fig-heawood-moves).


<a id="fig-heawood-moves"></a>


[D190: drawing](diagram-index.md#d190) **Figure caption.** Six Whitehead moves from our closure to the Heawood embedding. Colors and letters track the seven faces; $pq\to rs$ denotes the edge flip, with the sequence read row by row. Identify opposite dashed sides on the left, and boundary paths with matching letters on the right, following the arrows. The numbers record face lengths.

::: samepage
<a id="ai-statement-058"></a>


**Remark 7C.2.** [Source](source.tex#L6293); [PDF p. 34](source.pdf#page=34).


Our construction varies only the edge thicknesses. We suspect that things get considerably worse if the web graph itself is also allowed to grow, but we cannot yet prove a stronger growth statement this way. In the large-characteristic-setting considered here, Lübeck's argument bounds first cohomology dimensions for restricted irreducible modules by $2^{O(r^3)}$, where $r$ is the rank [[Lüb20](#bib-luebeck), Remark~(d) after Theorem~4.7]. There is plenty of room between this upper bound and our linear lower bound.
:::

The geometric idea helped us ask a more useful question, and the machine helped turn that idea into a family and a calculation that worked. Responsibility for the mathematics remains ours.


<a id="references"></a>

## References

<a id="bib-agrawalsotirov"></a>

### [AS21] `AgrawalSotirov`

```latex
R.~Agrawal and V.~Sotirov.
\newblock A generalization of {Deodhar}'s framework for questions in
{Kazhdan--Lusztig} theory.
\newblock 2021.
\newblock \url{https://arxiv.org/abs/2107.08522}.
```

[Link 1](https://arxiv.org/abs/2107.08522)

<a id="bib-andersen"></a>

### [And86] `Andersen`

```latex
H.~H.~Andersen.
\newblock An inversion formula for the {Kazhdan--Lusztig} polynomials
for affine {Weyl} groups.
\newblock {\em Adv. Math.}, 60(2):125--153, 1986.
\newblock \href
{https://doi.org/10.1016/S0001-8708(86)80008-1}
{\path{doi:10.1016/S0001-8708(86)80008-1}}.
```

[Link 1](https://doi.org/10.1016/S0001-8708(86)80008-1)

<a id="bib-ajs"></a>

### [AJS94] `AJS`

```latex
H.~H.~Andersen, J.~C.~Jantzen and W.~Soergel.
\newblock {\em Representations of quantum groups at a $p$th root of
unity and of semisimple groups in characteristic $p$:
independence of $p$}.
\newblock Ast\'erisque, vol.~220.
\newblock Soci\'et\'e math\'ematique de France, 1994.
```

<a id="bib-torsionproliferation"></a>

### [BT26] `TorsionProliferation`

```latex
J.~Baine and D.~Tubbenhauer.
\newblock Torsion proliferation.
\newblock 2026.
\newblock \url{https://arxiv.org/abs/2609.31781}.
```

[Link 1](https://arxiv.org/abs/2609.31781)

<a id="bib-blm"></a>

### [BLM90] `BLM`

```latex
A.~A.~Beilinson, G.~Lusztig and R.~MacPherson.
\newblock A geometric setting for the quantum deformation of
{$\operatorname{GL}_n$}.
\newblock {\em Duke Math. J.}, 61(2):655--677, 1990.
\newblock \href
{https://doi.org/10.1215/S0012-7094-90-06124-1}
{\path{doi:10.1215/S0012-7094-90-06124-1}}.
```

[Link 1](https://doi.org/10.1215/S0012-7094-90-06124-1)

<a id="bib-bendeletalhistory"></a>

### [B+14] `BendelEtAlHistory`

```latex
C.~P.~Bendel, B.~D.~Boe, C.~M.~Drupieski,
D.~K.~Nakano, B.~J.~Parshall, C.~Pillen and
C.~B.~Wright.
\newblock Bounding the dimensions of rational cohomology groups.
\newblock In {\em Developments and Retrospectives in Lie Theory},
Developments in Mathematics, vol.~38, pages 51--69.
Springer, 2014.
\newblock \href
{https://doi.org/10.1007/978-3-319-09804-3_2}
{\path{doi:10.1007/978-3-319-09804-3_2}}.
```

[Link 1](https://doi.org/10.1007/978-3-319-09804-3_2)

<a id="bib-bnp"></a>

### [BNP01] `BNP`

```latex
C.~P.~Bendel, D.~K.~Nakano and C.~Pillen.
\newblock On comparing the cohomology of algebraic groups, finite
{Chevalley} groups and {Frobenius} kernels.
\newblock {\em J. Pure Appl. Algebra}, 163(2):119--146, 2001.
\newblock \href
{https://doi.org/10.1016/S0022-4049(01)00024-X}
{\path{doi:10.1016/S0022-4049(01)00024-X}}.
```

[Link 1](https://doi.org/10.1016/S0022-4049(01)00024-X)

<a id="bib-bjornerbrentiaffine"></a>

### [BB05] `BjornerBrentiAffine`

```latex
A.~Bj{\"o}rner and F.~Brenti.
\newblock {\em Combinatorics of Coxeter Groups}.
\newblock Graduate Texts in Mathematics, vol.~231.
Springer, 2005.
\newblock \href
{https://doi.org/10.1007/3-540-27596-7}
{\path{doi:10.1007/3-540-27596-7}}.
```

[Link 1](https://doi.org/10.1007/3-540-27596-7)

<a id="bib-braywilson"></a>

### [BW08] `BrayWilson`

```latex
J.~N.~Bray and R.~A.~Wilson.
\newblock Examples of 3-dimensional 1-cohomology for absolutely
irreducible modules of finite simple groups.
\newblock {\em J. Group Theory}, 11(5):669--673, 2008.
\newblock \href
{https://doi.org/10.1515/JGT.2008.042}
{\path{doi:10.1515/JGT.2008.042}}.
```

[Link 1](https://doi.org/10.1515/JGT.2008.042)

<a id="bib-brundan"></a>

### [Bru25] `Brundan`

```latex
J.~Brundan.
\newblock The {$q$}-{Schur} category and polynomial tilting modules
for quantum {$\operatorname{GL}_n$}.
\newblock {\em Pacific J. Math.}, 336(1):63--112, 2025.
\newblock \url{https://arxiv.org/abs/2407.07228}, \href
{https://doi.org/10.2140/pjm.2025.336.63}
{\path{doi:10.2140/pjm.2025.336.63}}.
```

[Link 1](https://arxiv.org/abs/2407.07228) | [Link 2](https://doi.org/10.2140/pjm.2025.336.63)

<a id="bib-ck"></a>

### [CK18] `CK`

```latex
S.~Cautis and J.~Kamnitzer.
\newblock Quantum {$K$}-theoretic geometric {Satake}:
the {$\operatorname{SL}_n$} case.
\newblock {\em Compos. Math.}, 154(2):275--327, 2018.
\newblock \url{https://arxiv.org/abs/1509.00112}, \href
{https://doi.org/10.1112/S0010437X17007564}
{\path{doi:10.1112/S0010437X17007564}}.
```

[Link 1](https://arxiv.org/abs/1509.00112) | [Link 2](https://doi.org/10.1112/S0010437X17007564)

<a id="bib-ckm"></a>

### [CKM14] `CKM`

```latex
S.~Cautis, J.~Kamnitzer and S.~Morrison.
\newblock Webs and quantum skew {Howe} duality.
\newblock {\em Math. Ann.}, 360(1--2):351--390, 2014.
\newblock \url{https://arxiv.org/abs/1210.6437}, \href
{https://doi.org/10.1007/s00208-013-0984-4}
{\path{doi:10.1007/s00208-013-0984-4}}.
```

[Link 1](https://arxiv.org/abs/1210.6437) | [Link 2](https://doi.org/10.1007/s00208-013-0984-4)

<a id="bib-chen"></a>

### [Che18] `Chen`

```latex
P.~Chen.
\newblock Non-trivial {Kazhdan--Lusztig} coefficients of affine
{Weyl} groups.
\newblock 2018.
\newblock \url{https://arxiv.org/abs/1804.02353v2}.
```

[Link 1](https://arxiv.org/abs/1804.02353v2)

<a id="bib-cps"></a>

### [CPS09] `CPS`

```latex
E.~T.~Cline, B.~J.~Parshall and L.~L.~Scott.
\newblock Reduced standard modules and cohomology.
\newblock {\em Trans. Amer. Math. Soc.}, 361(10):5223--5261, 2009.
\newblock \href
{https://doi.org/10.1090/S0002-9947-09-04633-9}
{\path{doi:10.1090/S0002-9947-09-04633-9}}.
```

[Link 1](https://doi.org/10.1090/S0002-9947-09-04633-9)

<a id="bib-cui"></a>

### [Cui14] `Cui`

```latex
W.~Cui.
\newblock {Kazhdan--Lusztig} bases and the asymptotic forms
for affine {$q$}-{Schur} algebras.
\newblock 2014.
\newblock \url{https://arxiv.org/abs/1407.4557}.
```

[Link 1](https://arxiv.org/abs/1407.4557)

<a id="bib-deodhar"></a>

### [Deo87] `Deodhar`

```latex
V.~V.~Deodhar.
\newblock On some geometric aspects of {Bruhat} orderings. {II}.
{The} parabolic analogue of {Kazhdan--Lusztig} polynomials.
\newblock {\em J. Algebra}, 111(2):483--506, 1987.
\newblock \href
{https://doi.org/10.1016/0021-8693(87)90232-8}
{\path{doi:10.1016/0021-8693(87)90232-8}}.
```

[Link 1](https://doi.org/10.1016/0021-8693(87)90232-8)

<a id="bib-du"></a>

### [Du92] `Du`

```latex
J.~Du.
\newblock {Kazhdan--Lusztig} bases and isomorphism theorems
for {$q$}-{Schur} algebras.
\newblock In {\em Kazhdan--Lusztig Theory and Related Topics
(Chicago, 1989)}, Contemporary Mathematics, vol.~139,
pages 121--140. American Mathematical Society, 1992.
\newblock \href
{https://doi.org/10.1090/conm/139/1197832}
{\path{doi:10.1090/conm/139/1197832}}.
```

[Link 1](https://doi.org/10.1090/conm/139/1197832)

<a id="bib-dufu"></a>

### [DF15] `DuFu`

```latex
J.~Du and Q.~Fu.
\newblock Quantum affine {$\mathfrak{gl}_n$} via {Hecke} algebras.
\newblock {\em Adv. Math.}, 282:23--46, 2015.
\newblock \url{https://arxiv.org/abs/1311.1868}, \href
{https://doi.org/10.1016/j.aim.2015.06.007}
{\path{doi:10.1016/j.aim.2015.06.007}}.
```

[Link 1](https://arxiv.org/abs/1311.1868) | [Link 2](https://doi.org/10.1016/j.aim.2015.06.007)

<a id="bib-eliasko"></a>

### [EK23] `EliasKo`

```latex
B.~Elias and H.~Ko.
\newblock A singular {Coxeter} presentation.
\newblock {\em Proc. Lond. Math. Soc. (3)}, 126(3):923--996, 2023.
\newblock \url{https://arxiv.org/abs/2105.08563}, \href
{https://doi.org/10.1112/plms.12503}
{\path{doi:10.1112/plms.12503}}.
```

[Link 1](https://arxiv.org/abs/2105.08563) | [Link 2](https://doi.org/10.1112/plms.12503)

<a id="bib-fominpylyavskyy"></a>

### [FP14] `FominPylyavskyy`

```latex
S.~Fomin and P.~Pylyavskyy.
\newblock Webs on surfaces, rings of invariants, and clusters.
\newblock {\em Proc. Natl. Acad. Sci. USA}, 111(27):9680--9687, 2014.
\newblock \url{https://arxiv.org/abs/1308.1718}, \href
{https://doi.org/10.1073/pnas.1313068111}
{\path{doi:10.1073/pnas.1313068111}}.
```

[Link 1](https://arxiv.org/abs/1308.1718) | [Link 2](https://doi.org/10.1073/pnas.1313068111)

<a id="bib-fkk"></a>

### [FKK98] `FKK`

```latex
I.~B.~Frenkel, M.~G.~Khovanov and A.~A.~Kirillov, Jr.
\newblock {Kazhdan--Lusztig} polynomials and canonical basis.
\newblock {\em Transform. Groups}, 3(4):321--336, 1998.
\newblock \url{https://arxiv.org/abs/q-alg/9709042}, \href
{https://doi.org/10.1007/BF01234531}
{\path{doi:10.1007/BF01234531}}.
```

[Link 1](https://arxiv.org/abs/q-alg/9709042) | [Link 2](https://doi.org/10.1007/BF01234531)

<a id="bib-golatuva-mu-code-2"></a>

### [G+26a] `GoLaTuVa-mu-code-2`

```latex
T.~Goertzen, A.~Lacabanne, D.~Tubbenhauer and P.~Vaz.
\newblock {C}ode and more for the paper {A}nnular webs and
{G}uralnick's conjecture.
\newblock 2026. Accessed 26.Oct.2026.
\newblock \url{https://github.com/dtubbenhauer/mutwo}.
```

[Link 1](https://github.com/dtubbenhauer/mutwo)

<a id="bib-finite"></a>

### [G+26b] `Finite`

```latex
T.~Goertzen, A.~Lacabanne, D.~Tubbenhauer and P.~Vaz.
\newblock Exponentially large mu-coefficients.
\newblock 2026.
\newblock \url{https://arxiv.org/abs/2610.34982}.
```

[Link 1](https://arxiv.org/abs/2610.34982)

<a id="bib-greenaffine"></a>

### [Gre99] `GreenAffine`

```latex
R.~M.~Green.
\newblock The affine {$q$}-{Schur} algebra.
\newblock {\em J. Algebra}, 215(2):379--411, 1999.
\newblock \url{https://arxiv.org/abs/q-alg/9705015}, \href
{https://doi.org/10.1006/jabr.1998.7753}
{\path{doi:10.1006/jabr.1998.7753}}.
```

[Link 1](https://arxiv.org/abs/q-alg/9705015) | [Link 2](https://doi.org/10.1006/jabr.1998.7753)

<a id="bib-guralnick"></a>

### [Gur86] `Guralnick`

```latex
R.~M.~Guralnick.
\newblock The dimension of the first cohomology group.
\newblock In {\em Representation Theory II: Groups and Orders
(Ottawa, 1984)}, Lecture Notes in Mathematics, vol.~1178,
pages 94--97. Springer, 1986.
\newblock \href
{https://doi.org/10.1007/BFb0075290}
{\path{doi:10.1007/BFb0075290}}.
```

[Link 1](https://doi.org/10.1007/BFb0075290)

<a id="bib-aimwall"></a>

### [G+12] `AIMWall`

```latex
R.~M.~Guralnick, T.~Hodge, B.~J.~Parshall and L.~L.~Scott.
\newblock {AIM} workshop counterexample to {Wall}'s conjecture.
\newblock American Institute of Mathematics workshop report, 2012.
\newblock \url{https://www.mathinstitutes.org/highlights/disproof-of-walls-conjecture}.
```

[Link 1](https://www.mathinstitutes.org/highlights/disproof-of-walls-conjecture)

<a id="bib-guralnickhoffman"></a>

### [GH98] `GuralnickHoffman`

```latex
R.~M.~Guralnick and C.~Hoffman.
\newblock The first cohomology group and generation of simple groups.
\newblock In {\em Groups and geometries (Siena, 1996)},
Trends in Mathematics, pages 81--89. Birkh\"auser, 1998.
\newblock \href
{https://doi.org/10.1007/978-3-0348-8819-6_7}
{\path{doi:10.1007/978-3-0348-8819-6_7}}.
```

[Link 1](https://doi.org/10.1007/978-3-0348-8819-6_7)

<a id="bib-guralnicktiep"></a>

### [GT11] `GuralnickTiep`

```latex
R.~M.~Guralnick and P.~H.~Tiep.
\newblock First cohomology groups of {Chevalley} groups in
cross characteristic.
\newblock {\em Ann. of Math. (2)}, 174(1):543--559, 2011.
\newblock \href
{https://doi.org/10.4007/annals.2011.174.1.16}
{\path{doi:10.4007/annals.2011.174.1.16}}.
```

[Link 1](https://doi.org/10.4007/annals.2011.174.1.16)

<a id="bib-guralnicktiepsectional"></a>

### [GT20] `GuralnickTiepSectional`

```latex
R.~M.~Guralnick and P.~H.~Tiep.
\newblock Sectional rank and cohomology.
\newblock {\em J. Algebra}, 558:434--452, 2020.
\newblock \url{https://arxiv.org/abs/1807.07233}, \href
{https://doi.org/10.1016/j.jalgebra.2019.04.023}
{\path{doi:10.1016/j.jalgebra.2019.04.023}}.
```

[Link 1](https://arxiv.org/abs/1807.07233) | [Link 2](https://doi.org/10.1016/j.jalgebra.2019.04.023)

<a id="bib-ht"></a>

### [HT27] `HT`

```latex
D.~He and D.~Tubbenhauer.
\newblock Affine diagram categories, algebras and monoids.
\newblock {\em J. Algebra}, 712 (2027), 1050--1098.
\newblock \url{https://arxiv.org/abs/2512.05510}, \href
{https://doi.org/10.1016/j.jalgebra.2026.09.034}
{\path{doi:10.1016/j.jalgebra.2026.09.034}}.
```

[Link 1](https://arxiv.org/abs/2512.05510) | [Link 2](https://doi.org/10.1016/j.jalgebra.2026.09.034)

<a id="bib-jantzen2003"></a>

### [Jan03] `Jantzen2003`

```latex
J.~C.~Jantzen.
\newblock {\em Representations of Algebraic Groups}.
\newblock Mathematical Surveys and Monographs, vol.~107,
second edition. American Mathematical Society, 2003.
\newblock \href
{https://doi.org/10.1090/surv/107}
{\path{doi:10.1090/surv/107}}.
```

[Link 1](https://doi.org/10.1090/surv/107)

<a id="bib-kato"></a>

### [Kat82] `Kato`

```latex
S.-i.~Kato.
\newblock Spherical functions and a {$q$}-analogue of {Kostant}'s
weight multiplicity formula.
\newblock {\em Invent. Math.}, 66(3):461--468, 1982.
\newblock \href
{https://doi.org/10.1007/BF01389223}
{\path{doi:10.1007/BF01389223}}.
```

[Link 1](https://doi.org/10.1007/BF01389223)

<a id="bib-kl"></a>

### [KL79] `KL`

```latex
D.~Kazhdan and G.~Lusztig.
\newblock Representations of {Coxeter} groups and {Hecke} algebras.
\newblock {\em Invent. Math.}, 53(2):165--184, 1979.
\newblock \href
{https://doi.org/10.1007/BF01390031}
{\path{doi:10.1007/BF01390031}}.
```

[Link 1](https://doi.org/10.1007/BF01390031)

<a id="bib-kl80"></a>

### [KL80] `KL80`

```latex
D.~Kazhdan and G.~Lusztig.
\newblock Schubert varieties and {Poincar\'e} duality.
\newblock In {\em Geometry of the Laplace Operator},
Proceedings of Symposia in Pure Mathematics, vol.~36,
pages 185--203. American Mathematical Society, 1980.
```

<a id="bib-linkdetection"></a>

### [K+25] `LinkDetection`

```latex
T.~Kelom\"aki, A.~Lacabanne, D.~Tubbenhauer, P.~Vaz
and V.~L.~Zhang.
\newblock On detection probabilities of link invariants.
\newblock 2025.
\newblock \url{https://arxiv.org/abs/2509.05574}.
```

[Link 1](https://arxiv.org/abs/2509.05574)

<a id="bib-kk99"></a>

### [KK99] `KK99`

```latex
M.~Khovanov and G.~Kuperberg.
\newblock Web bases for {$\mathfrak{sl}(3)$} are not dual canonical.
\newblock {\em Pacific J. Math.}, 188(1):129--153, 1999.
\newblock \url{https://arxiv.org/abs/q-alg/9712046}, \href
{https://doi.org/10.2140/pjm.1999.188.129}
{\path{doi:10.2140/pjm.1999.188.129}}.
```

[Link 1](https://arxiv.org/abs/q-alg/9712046) | [Link 2](https://doi.org/10.2140/pjm.1999.188.129)

<a id="bib-kuperberg"></a>

### [Kup96] `Kuperberg`

```latex
G.~Kuperberg.
\newblock Spiders for rank 2 {Lie} algebras.
\newblock {\em Comm. Math. Phys.}, 180(1):109--151, 1996.
\newblock \href
{https://doi.org/10.1007/BF02101184}
{\path{doi:10.1007/BF02101184}}.
```

[Link 1](https://doi.org/10.1007/BF02101184)

<a id="bib-ltv"></a>

### [LTV23] `LTV`

```latex
A.~Lacabanne, D.~Tubbenhauer and P.~Vaz.
\newblock Annular webs and {Levi} subalgebras.
\newblock {\em J. Comb. Algebra}, 7(3--4):283--326, 2023.
\newblock \url{https://arxiv.org/abs/2204.00947}, \href
{https://doi.org/10.4171/JCA/76}
{\path{doi:10.4171/JCA/76}}.
```

[Link 1](https://arxiv.org/abs/2204.00947) | [Link 2](https://doi.org/10.4171/JCA/76)

<a id="bib-ltvbigdata"></a>

### [LTV26] `LTVBigData`

```latex
A.~Lacabanne, D.~Tubbenhauer and P.~Vaz.
\newblock Big data approach to {Kazhdan--Lusztig} polynomials.
\newblock {\em J. Exp. Math.}, 2(1):21--62, 2026.
\newblock \url{https://arxiv.org/abs/2412.01283}, \href
{https://doi.org/10.56994/JXM.002.001.002}
{\path{doi:10.56994/JXM.002.001.002}}.
```

[Link 1](https://arxiv.org/abs/2412.01283) | [Link 2](https://doi.org/10.56994/JXM.002.001.002)

<a id="bib-latifitubbenhauer"></a>

### [LT26] `LatifiTubbenhauer`

```latex
G.~Latifi and D.~Tubbenhauer.
\newblock Minimal presentations of $\mathfrak{gl}_n$-web categories.
\newblock {\em J. Knot Theory Ramifications},
35(12):2650028, 55~pp., 2026.
\newblock \url{https://arxiv.org/abs/2112.12688}, \href
{https://doi.org/10.1142/S0218216526500288}
{\path{doi:10.1142/S0218216526500288}}.
```

[Link 1](https://arxiv.org/abs/2112.12688) | [Link 2](https://doi.org/10.1142/S0218216526500288)

<a id="bib-luebeck"></a>

### [Lüb20] `Luebeck`

```latex
F.~L\"ubeck.
\newblock Computation of {Kazhdan--Lusztig} polynomials and some
applications to finite groups.
\newblock {\em Trans. Amer. Math. Soc.}, 373(4):2331--2347, 2020.
\newblock \url{https://arxiv.org/abs/1610.07055}, \href
{https://doi.org/10.1090/tran/8037}
{\path{doi:10.1090/tran/8037}}.
```

[Link 1](https://arxiv.org/abs/1610.07055) | [Link 2](https://doi.org/10.1090/tran/8037)

<a id="bib-lusztigbernstein"></a>

### [Lus89] `LusztigBernstein`

```latex
G.~Lusztig.
\newblock Affine {Hecke} algebras and their graded version.
\newblock {\em J. Amer. Math. Soc.}, 2(3):599--635, 1989.
\newblock \href
{https://doi.org/10.1090/S0894-0347-1989-0991016-9}
{\path{doi:10.1090/S0894-0347-1989-0991016-9}}.
```

[Link 1](https://doi.org/10.1090/S0894-0347-1989-0991016-9)

<a id="bib-lusztigaffine"></a>

### [Lus99] `LusztigAffine`

```latex
G.~Lusztig.
\newblock Aperiodicity in quantum affine {$\mathfrak{gl}_n$}.
\newblock {\em Asian J. Math.}, 3(1):147--177, 1999.
\newblock \href
{https://doi.org/10.4310/AJM.1999.v3.n1.a7}
{\path{doi:10.4310/AJM.1999.v3.n1.a7}}.
```

[Link 1](https://doi.org/10.4310/AJM.1999.v3.n1.a7)

<a id="bib-lusztigspherical"></a>

### [Lus83] `LusztigSpherical`

```latex
G.~Lusztig.
\newblock Singularities, character formulas, and a {$q$}-analog
of weight multiplicities.
\newblock {\em Ast\'erisque}, 101--102:208--229, 1983.
\newblock \url{https://www.numdam.org/item/AST_1983__101-102__208_0/}.
```

[Link 1](https://www.numdam.org/item/AST_1983__101-102__208_0/)

<a id="bib-macdonald"></a>

### [Mac95] `Macdonald`

```latex
I.~G.~Macdonald.
\newblock {\em Symmetric Functions and Hall Polynomials}.
\newblock Oxford Mathematical Monographs, second edition.
\newblock Oxford University Press, 1995.
\newblock \href
{https://doi.org/10.1093/oso/9780198534891.001.0001}
{\path{doi:10.1093/oso/9780198534891.001.0001}}.
```

[Link 1](https://doi.org/10.1093/oso/9780198534891.001.0001)

<a id="bib-mcgerty"></a>

### [McG03] `McGerty`

```latex
K.~McGerty.
\newblock Cells in quantum affine {$\mathfrak{sl}_n$}.
\newblock {\em Int. Math. Res. Not. IMRN}, 2003(24):1341--1361, 2003.
\newblock \url{https://arxiv.org/abs/math/0209055}, \href
{https://doi.org/10.1155/S107379280321120X}
{\path{doi:10.1155/S107379280321120X}}.
```

[Link 1](https://arxiv.org/abs/math/0209055) | [Link 2](https://doi.org/10.1155/S107379280321120X)

<a id="bib-nelsenram"></a>

### [NR03] `NelsenRam`

```latex
K.~Nelsen and A.~Ram.
\newblock {Kostka--Foulkes} polynomials and {Macdonald} spherical
functions.
\newblock In {\em Surveys in Combinatorics 2003}, London Mathematical
Society Lecture Note Series, vol.~307, pages 325--370.
Cambridge University Press, 2003.
\newblock \url{https://arxiv.org/abs/math/0401298}, \href
{https://doi.org/10.1017/CBO9781107359970.011}
{\path{doi:10.1017/CBO9781107359970.011}}.
```

[Link 1](https://arxiv.org/abs/math/0401298) | [Link 2](https://doi.org/10.1017/CBO9781107359970.011)

<a id="bib-parkerstewart"></a>

### [PS14] `ParkerStewart`

```latex
A.~E.~Parker and D.~I.~Stewart.
\newblock First cohomology groups for finite groups of {Lie} type
in defining characteristic.
\newblock {\em Bull. Lond. Math. Soc.}, 46(2):227--238, 2014.
\newblock \url{https://arxiv.org/abs/1211.6942}, \href
{https://doi.org/10.1112/blms/bdt087}
{\path{doi:10.1112/blms/bdt087}}.
```

[Link 1](https://arxiv.org/abs/1211.6942) | [Link 2](https://doi.org/10.1112/blms/bdt087)

<a id="bib-parshallscott"></a>

### [PS11] `ParshallScott`

```latex
B.~J.~Parshall and L.~L.~Scott.
\newblock Bounding {Ext} for modules for algebraic groups, finite
groups and quantum groups.
\newblock {\em Adv. Math.}, 226(3):2065--2088, 2011.
\newblock \url{https://arxiv.org/abs/0909.5207}, \href
{https://doi.org/10.1016/j.aim.2010.09.021}
{\path{doi:10.1016/j.aim.2010.09.021}}.
```

[Link 1](https://arxiv.org/abs/0909.5207) | [Link 2](https://doi.org/10.1016/j.aim.2010.09.021)

<a id="bib-queffelec"></a>

### [Que15] `Queffelec`

```latex
H.~Queffelec.
\newblock Skein modules from skew {Howe} duality and affine extensions.
\newblock {\em SIGMA}, 11:030, 36 pp., 2015.
\newblock \url{https://arxiv.org/abs/1309.4985}, \href
{https://doi.org/10.3842/SIGMA.2015.030}
{\path{doi:10.3842/SIGMA.2015.030}}.
```

[Link 1](https://arxiv.org/abs/1309.4985) | [Link 2](https://doi.org/10.3842/SIGMA.2015.030)

<a id="bib-rosetubbenhauer"></a>

### [RT16] `RoseTubbenhauer`

```latex
D.~E.~V.~Rose and D.~Tubbenhauer.
\newblock Symmetric webs, {Jones--Wenzl} recursions, and $q$-{Howe} duality.
\newblock {\em Int. Math. Res. Not. IMRN}, 2016(17):5249--5290, 2016.
\newblock \url{https://arxiv.org/abs/1501.00915}, \href
{https://doi.org/10.1093/imrn/rnv302}
{\path{doi:10.1093/imrn/rnv302}}.
```

[Link 1](https://arxiv.org/abs/1501.00915) | [Link 2](https://doi.org/10.1093/imrn/rnv302)

<a id="bib-scott"></a>

### [Sco03] `Scott`

```latex
L.~L.~Scott.
\newblock Some new examples in 1-cohomology.
\newblock {\em J. Algebra}, 260(1):416--425, 2003.
\newblock \href
{https://doi.org/10.1016/S0021-8693(02)00667-1}
{\path{doi:10.1016/S0021-8693(02)00667-1}}.

\begin{samepage}
```

[Link 1](https://doi.org/10.1016/S0021-8693(02)00667-1)

<a id="bib-scottsprowl"></a>

### [SS16] `ScottSprowl`

```latex
L.~L.~Scott and T.~Sprowl.
\newblock Computing individual {Kazhdan--Lusztig} basis elements.
\newblock {\em J. Symbolic Comput.}, 73:244--249, 2016.
\newblock \url{https://arxiv.org/abs/1309.7265}, \href
{https://doi.org/10.1016/j.jsc.2015.05.003}
{\path{doi:10.1016/j.jsc.2015.05.003}}.
\par
\end{samepage}
```

[Link 1](https://arxiv.org/abs/1309.7265) | [Link 2](https://doi.org/10.1016/j.jsc.2015.05.003)

<a id="bib-sx"></a>

### [SX10] `SX`

```latex
L.~L.~Scott and N.~Xi.
\newblock Some non-trivial {Kazhdan--Lusztig} coefficients of an
affine {Weyl} group of type {$\widetilde A_n$}.
\newblock {\em Sci. China Math.}, 53(8):1919--1930, 2010.
\newblock \url{https://arxiv.org/abs/0909.3394}, \href
{https://doi.org/10.1007/s11425-010-4041-4}
{\path{doi:10.1007/s11425-010-4041-4}}.
```

[Link 1](https://arxiv.org/abs/0909.3394) | [Link 2](https://doi.org/10.1007/s11425-010-4041-4)

<a id="bib-ssw"></a>

### [SSW25] `SSW`

```latex
Y.~Shen, L.~Song and W.~Wang.
\newblock Affine and cyclotomic {$q$}-{Schur} categories via webs.
\newblock 2025.
\newblock \url{https://arxiv.org/abs/2504.10270}.
```

[Link 1](https://arxiv.org/abs/2504.10270)

<a id="bib-songwangwebs"></a>

### [SW25] `SongWangWebs`

```latex
L.~Song and W.~Wang.
\newblock Affine and cyclotomic webs.
\newblock {\em J. Lond. Math. Soc. (2)}, 112(3):e70278, 2025.
\newblock \url{https://arxiv.org/abs/2406.13172}, \href
{https://doi.org/10.1112/jlms.70278}
{\path{doi:10.1112/jlms.70278}}.
```

[Link 1](https://arxiv.org/abs/2406.13172) | [Link 2](https://doi.org/10.1112/jlms.70278)

<a id="bib-springer82"></a>

### [Spr82] `Springer82`

```latex
T.~A.~Springer.
\newblock Quelques applications de la cohomologie d'intersection.
\newblock {\em Ast\'erisque}, 92--93:249--273, 1982.
\newblock S\'eminaire Bourbaki, Exp.\ no.~589.
```

<a id="bib-steinbergyale"></a>

### [Ste16] `SteinbergYale`

```latex
R.~Steinberg.
\newblock {\em Lectures on Chevalley Groups}.
\newblock Notes prepared by J.~Faulkner and R.~Wilson.
University Lecture Series, vol.~66.
American Mathematical Society, 2016.
\newblock \href
{https://doi.org/10.1090/ulect/066}
{\path{doi:10.1090/ulect/066}}.
```

[Link 1](https://doi.org/10.1090/ulect/066)

<a id="bib-steinberg"></a>

### [Ste63] `Steinberg`

```latex
R.~Steinberg.
\newblock Representations of algebraic groups.
\newblock {\em Nagoya Math. J.}, 22:33--56, 1963.
\newblock \href
{https://doi.org/10.1017/S0027763000011016}
{\path{doi:10.1017/S0027763000011016}}.
```

[Link 1](https://doi.org/10.1017/S0027763000011016)

<a id="bib-tu-qt"></a>

### [Tub25] `Tu-qt`

```latex
D.~Tubbenhauer.
\newblock Quantum topology without topology.
\newblock 2025.
\newblock \url{https://arxiv.org/abs/2506.18918}.
```

[Link 1](https://arxiv.org/abs/2506.18918)

<a id="bib-sandwich"></a>

### [Tub24] `Sandwich`

```latex
D.~Tubbenhauer.
\newblock Sandwich cellularity and a version of cell theory.
\newblock {\em Rocky Mountain J. Math.}, 54(6):1733--1773, 2024.
\newblock \url{https://arxiv.org/abs/2206.06678}, \href
{https://doi.org/10.1216/rmj.2024.54.1733}
{\path{doi:10.1216/rmj.2024.54.1733}}.
```

[Link 1](https://arxiv.org/abs/2206.06678) | [Link 2](https://doi.org/10.1216/rmj.2024.54.1733)

<a id="bib-tvw"></a>

### [TVW17] `TVW`

```latex
D.~Tubbenhauer, P.~Vaz and P.~Wedrich.
\newblock Super $q$-{Howe} duality and web categories.
\newblock {\em Algebr. Geom. Topol.}, 17(6):3703--3749, 2017.
\newblock \url{https://arxiv.org/abs/1504.05069}, \href
{https://doi.org/10.2140/agt.2017.17.3703}
{\path{doi:10.2140/agt.2017.17.3703}}.
```

[Link 1](https://arxiv.org/abs/1504.05069) | [Link 2](https://doi.org/10.2140/agt.2017.17.3703)

<a id="bib-williamson"></a>

### [Wil11] `Williamson`

```latex
G.~Williamson.
\newblock Singular {Soergel} bimodules.
\newblock {\em Int. Math. Res. Not. IMRN}, 2011(20):4555--4632, 2011.
\newblock \url{https://arxiv.org/abs/1010.1283}, \href
{https://doi.org/10.1093/imrn/rnq263}
{\path{doi:10.1093/imrn/rnq263}}.
```

[Link 1](https://arxiv.org/abs/1010.1283) | [Link 2](https://doi.org/10.1093/imrn/rnq263)

<a id="bib-yamada"></a>

### [Yam89] `Yamada`

```latex
S.~Yamada.
\newblock An invariant of spatial graphs.
\newblock {\em J. Graph Theory}, 13(5):537--551, 1989.
\newblock \href
{https://doi.org/10.1002/jgt.3190130503}
{\path{doi:10.1002/jgt.3190130503}}.
```

[Link 1](https://doi.org/10.1002/jgt.3190130503)
