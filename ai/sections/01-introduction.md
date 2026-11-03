# 1. Introduction

Part of *Annular webs and Guralnick's conjecture*, snapshot 2026-11-03. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.

<a id="section-1"></a>

## 1. Introduction

<!-- Source: source.tex lines 2815; PDF page 1. -->


We use webs on an annulus to disprove Guralnick's 1986 conjecture, a classical problem about finite groups, far from the usual home of webs.


<a id="section-1a"></a>

### 1A. The question

<!-- Source: source.tex lines 2820; PDF page 1. -->


How large can the first cohomology of a finite group be? Let $G$ be a finite group, $k$ a field and $M$ a finite-dimensional $kG$-module. The space $H^1(G,M)=\operatorname{Ext}^1_{kG}(k,M)$ classifies extensions $0\to M\to E\to k\to0$, where $k$ is the trivial module. Thus $H^1(G,M)=0$ precisely when every such extension splits. We ask about its dimension when $M$ is as easy as possible: faithful and absolutely irreducible.

<a id="ai-statement-001"></a>


**Remark 1A.1.** [Source](../source.tex#L2830); [PDF p. 1](../source.pdf#page=1).


First cohomology also has a concrete interpretation in terms of subgroups. Regard $M$ as an additive group and form the semidirect product $M\rtimes G$. Then $H^1(G,M)$ parametrizes the complements to $M$, up to conjugation by elements of $M$. This connects cohomology dimensions with the subgroup structure of finite groups.

In 1986, Guralnick conjectured that there is an absolute constant $C$ such that $\dim_k H^1(G,M)\le C$ for every finite group $G$, every field $k$ and every finite-dimensional faithful absolutely irreducible $kG$-module $M$ [[Gur86](../paper.md#bib-guralnick), Conjecture~2]; see also [[Lüb20](../paper.md#bib-luebeck), Conjecture~4.4]. The same constant must work regardless of the group, its rank, the characteristic or the dimension of the module. We call this *Guralnick's conjecture*.

The known dimensions were initially small enough for Guralnick--Hoffman to conjecture $C=2$ [[GH98](../paper.md#bib-guralnickhoffman), Conjecture~2]. Scott disproved this in 2003 [[Sco03](../paper.md#bib-scott)], and Bray--Wilson later gave explicit modules with first cohomology of dimension three [[BW08](../paper.md#bib-braywilson)]. Subsequent computations produced much larger values. Lübeck obtained dimensions $469$ and $36672$ in types $A_7$ and $A_8$, and $3{,}537{,}142$ in type $E_6$, in sufficiently large defining characteristic [[Lüb20](../paper.md#bib-luebeck), Theorem~4.7]. These calculations suggested rapid growth with the rank, but pushing them further is difficult: even a single relevant KL polynomial can require substantial time and memory [[Lüb20](../paper.md#bib-luebeck), [SS16](../paper.md#bib-scottsprowl)].

<a id="ai-statement-002"></a>


**Remark 1A.2.** [Source](../source.tex#L2864); [PDF p. 1](../source.pdf#page=1).


Large first cohomology dimensions also led to counterexamples to Wall's conjecture on maximal subgroups at the 2012 AIM workshop "Cohomology bounds and growth rates". For the story and its connection with Guralnick's conjecture, see e.g. [[G+12](../paper.md#bib-aimwall), [B+14](../paper.md#bib-bendeletalhistory)].

To disprove Guralnick's conjecture, one needs a family whose cohomology dimensions are unbounded. Our explicit family gives such a result:


<a id="cor-intro-guralnick"></a>


**Corollary 1A.3.** (See [Corollary 6C.2](../paper.md#cor-guralnick)) [Source](../source.tex#L2875); [PDF p. 2](../source.pdf#page=2).


For each $m\ge2$ and every sufficiently large prime $p$, there is a faithful absolutely irreducible module $M$ for $H=\mathrm{PSL}_{2m+1}(\mathbb F_p)$ over $k=\overline{\mathbb F}_p$ such that 

```latex
\dim_k H^1(H,M)\ge\left\lceil\frac{m+1}{2}\right\rceil.
```

 In particular, Guralnick's absolute boundedness conjecture is false.

The growth is linear in the rank, and the required threshold for $p$ may depend on $m$, so both the rank and the characteristic vary in this construction. The highest weights of the modules are explicit; they are given in [Section 6](../paper.md#sec-guralnick).

Perhaps more striking is how the counterexamples arise: from the right perspective, the conjecture is "almost obviously false". We use a fixed web (a convenient way of writing a linear map) graph drawn on an annulus, with inputs on the inner boundary and outputs on the outer boundary. The local vertices are splits and merges, but they can meet around the annulus. Crazy enough, in our construction the graph stays the same as $m$ grows; only the edge thicknesses change. And the graph is tiny: its natural toroidal closure (after applying two ordinary merges) has just 14 vertices and 21 edges, exactly like the famous Heawood graph, although the two are not isomorphic, cf. [Figure 1](../paper.md#fig-toroidal-closure).


<a id="fig-toroidal-closure"></a>


[D001: drawing](../diagram-index.md#d001)

**Figure caption.** The toroidal closure of our web graph. Opposite dashed sides are identified. The graph has $14$ vertices, $21$ edges and seven faces of lengths $4,4,5,5,6,6,12$.

Using the canonical expansion of this web, we compute the sum of a family of $m$ affine Kazhdan--Lusztig (KL) $\mu$-coefficients [[KL79](../paper.md#bib-kl)]. The sum is exactly $m(m+1)/2$, so at least one coefficient is at least $\lceil(m+1)/2\rceil$. This gives the cohomological lower bound. Finally, for the modules considered here, in sufficiently large characteristic, the first cohomology dimension then equals this affine $\mu$-coefficient.

<a id="ai-statement-004"></a>


**Remark 1A.4.** [Source](../source.tex#L3061); [PDF p. 2](../source.pdf#page=2).


In [[G+26b](../paper.md#bib-finite)], we also use webs to prove exponential growth for $\mu$-coefficients of finite symmetric groups. The difference essentially is that in [[G+26b](../paper.md#bib-finite)] we use planar webs, fix the rank and let the web grow, while in this paper we use annular webs, fix the web and let the rank grow. (The idea that "planar = finite" and "annular = affine" has been around for donkey's years in low-dimensional topology; see [[HT27](../paper.md#bib-ht), Section~1B] for a brief historical overview.)

Note that Scott--Xi [[SX10](../paper.md#bib-sx)] constructed unbounded affine $\mu$-coefficients in type $A$, and Chen [[Che18](../paper.md#bib-chen)] treated the other classical affine types. None of [[Che18](../paper.md#bib-chen), [G+26b](../paper.md#bib-finite), [SX10](../paper.md#bib-sx)] can be directly used to refute Guralnick's conjecture.

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

 [D002](../diagram-index.md#d002); [D003](../diagram-index.md#d003)

 The gray line becomes the gluing circle, with $s_1$ in the inner band and $s_0$ in the outer band. The boundary labels are residues modulo five: the strings from $2$ and $5$ reach the points labeled $5$ and $1$, representing $0$ and $6$. The winding distinguishes these integers from their residues. Here $\ell(s_0s_1)=2$. The precise conventions are in [Section 2](../paper.md#sec-dictionary), following [[HT27](../paper.md#bib-ht), Section~2A].


<a id="section-1c"></a>

### 1C. The main result in more detail

<!-- Source: source.tex lines 3182; PDF page 3. -->


For our main result, we need to construct two annular permutations, the lower and upper endpoint. For first cohomology we need $w_0$ as the lower endpoint, corresponding to the trivial module, see e.g. [[SX10](../paper.md#bib-sx), Section~4], which is fixed throughout. We construct the upper endpoints by shifting entries of $[1,\ldots,N]$ by one period and sorting. For $1\le j\le m$, set 

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

 The two representatives at $m=2$ are drawn in [Figure 2](../paper.md#fig-intro-example). As we will see below, although these annular permutations look fairly complicated, their annular web pictures are surprisingly easy.

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


**Theorem 1C.1.** (See [Theorem 4L.1](../paper.md#thm-aggregate-web)) [Source](../source.tex#L3223); [PDF p. 3](../source.pdf#page=3).


For every $m\ge2$, the family above satisfies 

```latex
\sum_{j=1}^{m}\mu_{j;m}=\frac{m(m+1)}{2}.
```

 In particular, $\lceil(m+1)/2\rceil\leq\max_{1\le j\le m}\mu_{j;m}$.

Our proof computes the row sum without determining its individual terms. [Theorem 1C.1](../paper.md#thm-intro) then implies [Corollary 1A.3](../paper.md#cor-intro-guralnick), as explained in [Section 6](../paper.md#sec-guralnick).

Exact computations give the following for $2\le m\le5$; see [Section 1F](../paper.md#s-lean) for the code and Lean verification. 

```latex
\begin{array}{c|cccc}
m&2&3&4&5\\\hline
N&5&7&9&11\\
(\mu_{1;m},\ldots,\mu_{m;m})&(1,2)&(1,2,3)&(1,2,3,4)&(1,2,3,4,5)\\
\text{row sum}&3&6&10&15
\end{array}
```

 The theorem proves the row sums for all $m$. (The computed rows suggest $\mu_{j;m}=j$, but we don't know whether this is true for general $m$.) At $m=2$, for instance, $P_{w_0,C_{2;2}}(Q)=1+4Q+5Q^2+4Q^3+2Q^4$. Here $D_{2;2}=9$, so $\mu_{2;2}$ is the coefficient of $Q^4$, namely two. This is the Scott--Xi example [[SX10](../paper.md#bib-sx), Lemma~3.4], recovered below using webs.


<a id="fig-intro-example"></a>


  ---------------------- ----------------------
   $u_{1;2}=[-1,1,3,5,7]$   $u_{2;2}=[-4,-1,3,7,10]$
   $\text{[D004]}\;\text{[D005]}$ [D004](../diagram-index.md#d004); [D005](../diagram-index.md#d005)   $\text{[D006]}\;\text{[D007]}$ [D006](../diagram-index.md#d006); [D007](../diagram-index.md#d007)
  ---------------------- ----------------------

**Figure caption.** The first two representatives, each shown in one period and on the annulus. Composing with $w_0$ at the inner boundary gives the upper endpoints $C_{j;2}$.


<a id="section-1d"></a>

### 1D. The web picture

<!-- Source: source.tex lines 3316; PDF page 4. -->


Recall that a web is a graph with labeled edges and trivalent internal vertices. Its boundary is recorded by the sequence of incident edge labels or thicknesses, say $(a,b,c)$. In a symmetric web, an edge labeled $a$ represents the $a$th symmetric power of the representation carried by a thin label $1$ strand, see e.g. [[RT16](../paper.md#bib-rosetubbenhauer), [TVW17](../paper.md#bib-tvw)]. Thickness is conserved at each vertex: a split replaces $(a+b)$ by $(a,b)$, and a merge does the reverse. We use the annular construction of, for example, [[Que15](../paper.md#bib-queffelec), [LTV23](../paper.md#bib-ltv)] with symmetric rather than exterior edges, reading from the inner boundary outwards.

Our web $\mathcal R_m:(N)\to(m,1,m)$ is built as follows: Split into $(m,1,m)$ and merge the two $m$-edges across the cut. Expose two more unit strands to obtain $(1,m-1,1,m-1,1)$. Keep the two outer units separate while merging and splitting the middle three edges. Finally, rejoin each retained unit to its neighboring edge. See [Figure 3](../paper.md#fig-intro-affine-construction) for an illustration.


<a id="fig-intro-affine-construction"></a>


  ---------------------- ------------------------ ------------------------
    \(a\) First split     \(b\) Expose two units   \(c\) Complete the web
   $(2,1,2)$    $(1,1,1,1,1)$     $(2,1,2)$
   $\text{[D008]}$ [D008](../diagram-index.md#d008)    $\text{[D009]}$ [D009](../diagram-index.md#d009)     $\text{[D010]}$ [D010](../diagram-index.md#d010)
   $(3,1,3)$    $(1,2,1,2,1)$     $(3,1,3)$
   $\text{[D011]}$ [D011](../diagram-index.md#d011)    $\text{[D012]}$ [D012](../diagram-index.md#d012)     $\text{[D013]}$ [D013](../diagram-index.md#d013)
  ---------------------- ------------------------ ------------------------

**Figure caption.** Three stages of $\mathcal R_2$ (top) and $\mathcal R_3$ (bottom). The sequences give the output boundaries; the inputs are $(5)$ and $(7)$, respectively. Blue strands have thickness one. The two outer unit strands exposed in (b) are retained through the merge and split.

The displayed intermediate boundaries, together with the blue labels $1$, determine every omitted internal label by conservation at the vertices. For example, at $m=3$ the cyclic merge has thickness $6$ and the middle merge has thickness $5$. As [Figure 4](../paper.md#fig-intro-annular-family) shows, the graph stays fixed as $m$ grows; only the edge thicknesses change. The six maps are given in [Section 3](../paper.md#sec-algebraic-gallery).


<a id="fig-intro-annular-family"></a>


$\displaystyle
\mathcal R_m:(N)\longrightarrow(m,1,m),\qquad N=2m+1.$

  ---------------------- ----------------------
         Annulus            Cut-open annulus
   $\vcenter{\hbox{\text{[D014]}}}$ [D014](../diagram-index.md#d014)   $\vcenter{\hbox{ 
\text{[D015]}}}$ [D015](../diagram-index.md#d015)
  ---------------------- ----------------------

**Figure caption.** The same web $\mathcal R_m$ in two forms. Glue the red dashed sides of the right-hand picture at equal heights to recover the annulus on the left. The blue strands have thickness one.


<a id="section-1e"></a>

### 1E. The proof in a nutshell

<!-- Source: source.tex lines 3391; PDF page 4. -->


The starting point is the relation between canonical bases and KL polynomials. In [[G+26b](../paper.md#bib-finite)], we used the theorem of Frenkel--Khovanov--Kirillov (FKK) [[FKK98](../paper.md#bib-fkk)], relating canonical bases in tensor powers to KL polynomials for symmetric groups. Here we need an annular counterpart. We obtain it from the canonical basis of affine Schur theory, using the Hecke realization of annular symmetric webs, see e.g. [[Cui14](../paper.md#bib-cui), [Lus99](../paper.md#bib-lusztigaffine), [SSW25](../paper.md#bib-ssw)]. We explain the comparison and its normalization in [Section 2](../paper.md#sec-dictionary).

For fixed input and output labels, the relevant web morphism space has a normalized standard basis $[A]_v$ and a canonical basis $\theta_A$. Their indices are affine double cosets determined by the boundary labels. As in KL theory, the canonical basis is characterized by bar invariance and triangularity with respect to the standard basis.

Only one standard coefficient will matter. Let $b_m(f)$ denote the coefficient of $[B_m]_v$ in the standard expansion of $f$, where $B_m:(N)\to(m,1,m)$ is the ordinary split map, called splitter. This splitter is both standard and canonical. Its input packet corresponds to the finite parabolic subgroup $S_N$, and its longest double-coset representative is $w_0$. For the index $A_{j;m}$ corresponding to our upper endpoint $C_{j;m}$, the comparison gives 

```latex
b_m(\theta_{A_{j;m}})
=v^{D_{j;m}}P_{w_0,C_{j;m}}(v^{-2}).
```

 The highest allowed KL degree becomes the coefficient of $v$: thus $[v]\,b_m(\theta_{A_{j;m}})=\mu_{j;m}$. This explains both the choice of the ordinary splitter and the normalization.

Our web $\mathcal R_m$ is bar invariant, but it need not be a canonical element. Lower canonical terms can affect the coefficient we want, just as in [[G+26b](../paper.md#bib-finite)]. Already at $m=2$, $b_2(\mathcal R_2)=v^{-1}+4v+7v^3+\cdots$. The ordinary splitter occurs with multiplicity $v+v^{-1}$. Subtracting it gives $b_2(\mathcal R_2^{\rm crit})=3v+7v^3+\cdots$. Reading the coefficient before this correction would give four; the desired sum is three.


<a id="fig-intro-critical-correction"></a>


$\displaystyle
\mathcal R_2^{\rm crit}=
\text{[D016]}
\quad-(v+v^{-1})
\text{[D017]}.$ [D016](../diagram-index.md#d016); [D017](../diagram-index.md#d017)

**Figure caption.** The first correction in $\operatorname{Hom}((5),(2,1,2))$. Subtracting the ordinary splitter leaves the two desired canonical summands and two auxiliary terms, each retaining one line. The auxiliary contributions start in degree three. The individual $\mu$-coefficients are recovered in [Section 5](../paper.md#sec-aggregate-calibration).

For general $m$, we first compute the standard expansion of $\mathcal R_m$. The split and merge maps describe choices of intermediate flags between fixed input and output flags. Here a flag is a chain of nested subspaces. We fix the input and output flags and count the intermediate choices prescribed by the splits and merges over a finite field $\mathbb F_Q$. For example, an $n$-dimensional space has $\genfrac{[}{]}{0pt}{}{n}{k}_Q$ subspaces of dimension $k$. Requiring a subspace to contain a fixed subspace $U$ amounts to making the corresponding choice in the quotient by $U$. Counting the required lines, hyperplanes and subspaces in this way gives expressions in Gaussian binomial coefficients, also called $q$-binomials. We then substitute $Q=v^{-2}$; the normalization supplies the remaining powers of $v$. These counts are carried out in [Section 3](../paper.md#sec-algebraic-gallery).

We then determine which canonical elements can occur. If $\mathcal R_m=\sum_A M_A(v)\theta_A$, bar invariance gives $M_A(v)=M_A(v^{-1})$. Together with KL positivity, this turns the degree bounds from the standard calculation into bounds on the multiplicities $M_A$. Only six families survive. One consists of our $m$ elements $\theta_{A_{j;m}}$. Comparing constant coefficients at their standard indices proves that each occurs once.

Four auxiliary families retain one line or impose the dual hyperplane condition. Even after multiplication by their Laurent polynomial multiplicities, their contributions at $B_m$ start in degree three. They therefore do not affect the coefficient of $v$.

The remaining family does affect it. Its webs have one packet of thickness $N$ at both ends, before the ordinary output split. Apart from the initial splitter $B_m$, its canonical elements are differences of consecutive split--merge webs. We determine their multiplicities by successively canceling nonpositive powers in the corresponding standard coefficients; bar symmetry determines the positive powers. Subtracting this family gives 

```latex
\mathcal R_m^{\rm crit}
=\sum_{j=1}^{m}\theta_{A_{j;m}}+E_m,
\qquad b_m(E_m)\in v^3\mathbb Z[v],
```

 where $E_m$ collects the four auxiliary families with a retained line or its dual.

It remains to compute the linear coefficient of the corrected standard expansion. The Gaussian cancellation in [Section 4](../paper.md#sec-algebraic-relevance) gives 

```latex
\sum_{j=1}^{m}\mu_{j;m}
=[v]\,b_m(\mathcal R_m^{\rm crit})
=[z^{m-1}]\frac{1}{(1-z)^3}
=\binom{m+1}{2}.
```

 The last coefficient counts triples of nonnegative integers summing to $m-1$. Thus the calculation gives the whole row sum without requiring a formula for its individual entries.

<a id="ai-statement-006"></a>


**Remark 1E.1.** [Source](../source.tex#L3531); [PDF p. 7](../source.pdf#page=7).


This paper continues [[G+26b](../paper.md#bib-finite)], but can be read independently. Both papers follow roughly the same strategy with the following differences. 

```latex
\text{[D018]}
```

 [D018](../diagram-index.md#d018)

 In both cases, webs serve as a visual guide.


<a id="section-1f"></a>

### 1F. Computations and Lean verification

<!-- Source: source.tex lines 3540; PDF page 7. -->


<a id="s-lean"></a>


This paper builds on [[G+26b](../paper.md#bib-finite), [LTV26](../paper.md#bib-ltvbigdata)]. The accompanying computational tools and Lean formalization are collected in [[G+26a](../paper.md#bib-golatuva-mu-code-2)]. The formalization verifies the main algebraic and cohomological argument relative to explicitly stated hypotheses from the literature; see [Remark 1F.1](../paper.md#rem-verification).


<a id="rem-verification"></a>


**Remark 1F.1.** [Source](../source.tex#L3549); [PDF p. 7](../source.pdf#page=7).


The Lean formalization verifies the explicit affine family, the six-map web calculation, the gallery counts, the canonical correction and the row-sum identity for every $m\ge2$. It also formalizes the deduction of faithful absolutely irreducible modules with unbounded first cohomology. In addition, it verifies the rank-one correction and the five-term canonical expansion in [Section 5](../paper.md#sec-aggregate-calibration), and proves the two ordinary KL polynomial identities for $m=2$, with lower endpoint $w_0$.

The remaining unformalized results from the literature are supplied as explicit hypotheses. These include the affine Coxeter realization, KL theory and positivity, canonical Schur bases and their compatibility with refinement, and flag-orbit classification and Hecke convolution. For the cohomological application, we use highest weight theory, restricted irreducibility, the eventual character formula, the KL-to-$H^1$ identification, rational cohomology via the Hochschild complex, comparison with finite group cohomology, and simplicity of the relevant projective special linear groups.

These background results are not formalized. The cohomological deduction retains the fixed trivial source and the stated characteristic bounds. References for the external inputs are [[And86](../paper.md#bib-andersen), [AJS94](../paper.md#bib-ajs), [BNP01](../paper.md#bib-bnp), [BB05](../paper.md#bib-bjornerbrentiaffine), [Cui14](../paper.md#bib-cui), [Jan03](../paper.md#bib-jantzen2003), [KL79](../paper.md#bib-kl), [KL80](../paper.md#bib-kl80), [Lüb20](../paper.md#bib-luebeck), [Lus99](../paper.md#bib-lusztigaffine), [Spr82](../paper.md#bib-springer82), [Ste63](../paper.md#bib-steinberg), [Ste16](../paper.md#bib-steinbergyale), [Wil11](../paper.md#bib-williamson)]. The citations are not necessarily to the original sources.

The Lean development also encodes the chosen web as a labeled graph and proves that its specified presentation evaluates to the six-map morphism used in the calculation.


<a id="acknowledgments"></a>

### Acknowledgments

<!-- Source: source.tex lines 3586; PDF page 7. -->


We thank the ANU Kioloa Coastal Campus, where the common interest of TG and DT was discovered at a workshop organized by Anthony Licata and Oded Yacobi. We thank Keeley Hoek for helping with translating C code into very efficient Rust code for computing $W$-graphs, and Lukas Lewark for making the `webdraw` program available for computing Kuperberg polynomials.

TG acknowledges funding by the Australian Government through ARC DP230102982. DT was supported by ARC Future Fellowship FT230100489 and asserts that no large language models were injured in the making of this paper (just one very tired human). P.V. is supported by FNRS (Belgium) Grant no. J.0235.26.


