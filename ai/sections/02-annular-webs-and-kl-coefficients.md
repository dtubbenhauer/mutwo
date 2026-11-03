# 2. Annular webs and KL coefficients

Part of *Annular webs and Guralnick's conjecture*, snapshot 2026-11-03. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.

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

 [D019](../diagram-index.md#d019); [D020](../diagram-index.md#d020); [D021](../diagram-index.md#d021); [D022](../diagram-index.md#d022)

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

 [D023](../diagram-index.md#d023); [D024](../diagram-index.md#d024); [D025](../diagram-index.md#d025)

 Cutting the annulus open gives a rectangle with its vertical sides identified, and planar diagrams embed on such a rectangle. Matching seam labels mark continuations of the same edge at the same height. The cut fixes the start of each ordered boundary. For example, gluing the boundary $(3)$ gives 

```latex
\begin{gather*}
\text{[D026]}\ \circ\ \text{[D027]}
=\text{[D028]}
\quad\xleftrightarrow{\text{cut / glue}}\quad\text{[D029]}.
\end{gather*}
```

 [D026](../diagram-index.md#d026); [D027](../diagram-index.md#d027); [D028](../diagram-index.md#d028); [D029](../diagram-index.md#d029)

 The input and output are $(1,2)$. In an annular hole, a gray arrow connects an input label to its endpoint.

Freer drawings, with bent or horizontal segments, abbreviate upward webs. After isotopy, and cutting open in the annular case, all edges can be made to run upwards. We use no cups, caps or closed components. For example:

$\displaystyle \text{[D030]}
\quad\xleftrightarrow{\text{isotopy}}\quad
\text{[D031]}.$ [D030](../diagram-index.md#d030); [D031](../diagram-index.md#d031)


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


**Definition 2B.1.** [Source](../source.tex#L3739); [PDF p. 9](../source.pdf#page=9).


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

 [D032](../diagram-index.md#d032); [D033](../diagram-index.md#d033); [D034](../diagram-index.md#d034); [D035](../diagram-index.md#d035)

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

 [D036](../diagram-index.md#d036); [D037](../diagram-index.md#d037); [D038](../diagram-index.md#d038); [D039](../diagram-index.md#d039); [D040](../diagram-index.md#d040); [D041](../diagram-index.md#d041); [D042](../diagram-index.md#d042); [D043](../diagram-index.md#d043)

 The crossing in a summand is $H_{i,j}$.

<a id="ai-statement-009"></a>


**Remark 2B.3.** [Source](../source.tex#L3814); [PDF p. 9](../source.pdf#page=9).


Webs have been around for a long time, see e.g. [[Yam89](../paper.md#bib-yamada)]. The above is the integral presentation of [[LT26](../paper.md#bib-latifitubbenhauer), Section~5], in the crossing normalization of [[Bru25](../paper.md#bib-brundan), Theorem~1] and [[SSW25](../paper.md#bib-ssw), (2.4)--(2.6)]. For exterior webs see [[CKM14](../paper.md#bib-ckm), [Kup96](../paper.md#bib-kuperberg)]; for symmetric and mixed webs see [[RT16](../paper.md#bib-rosetubbenhauer), [TVW17](../paper.md#bib-tvw), [Tub25](../paper.md#bib-tu-qt)], among many others.

On $\omega_N$, let $H_i$ denote the positive crossing in positions $i,i+1$, and $b_i$ the thin merge followed by a split. Products of these diagrams mean stacking, with the rightmost factor applied first.


<a id="lem-thin-hecke-relations"></a>


**Lemma 2B.4.** [Source](../source.tex#L3828); [PDF p. 9](../source.pdf#page=9).


The Schur relation at $a=b=c=d=1$ gives


<a id="eq-thin-channel-normalization"></a>


```latex
\begin{gather}
b_i=\text{[D044]}
=\text{[D045]}+v\,\text{[D046]}\hspace{.6cm}\text{[D047]}
=H_i+v.
\end{gather}
```

 [D044](../diagram-index.md#d044); [D045](../diagram-index.md#d045); [D046](../diagram-index.md#d046); [D047](../diagram-index.md#d047)

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

 [D048](../diagram-index.md#d048); [D049](../diagram-index.md#d049); [D050](../diagram-index.md#d050); [D051](../diagram-index.md#d051); [D052](../diagram-index.md#d052); [D053](../diagram-index.md#d053); [D054](../diagram-index.md#d054)

 Crossings can be expressed using splits and merges and can therefore be omitted as generators.

**Proof.**

The first identity is the two-term Schur relation. Contracting the middle digon gives $b_i^2=[2]b_i$, hence the quadratic relation. Distant crossings commute by juxtaposition. The remaining statements follow from [[LT26](../paper.md#bib-latifitubbenhauer), Section~5] after changing normalization.

*End of proof.*

[Lemma 2B.4](../paper.md#lem-thin-hecke-relations) gives the Hecke relations: 

```latex
\begin{gather*}
(H_i-v^{-1})(H_i+v)=0,\qquad
H_iH_j=H_jH_i\,(|i-j|>1)\qquad H_iH_jH_i=H_jH_iH_j\,(|i-j|=1).
\end{gather*}
```


<a id="lem-iterated-web-digons"></a>


**Lemma 2B.6.** [Source](../source.tex#L3862); [PDF p. 10](../source.pdf#page=10).


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

 [D055](../diagram-index.md#d055); [D056](../diagram-index.md#d056); [D057](../diagram-index.md#d057); [D058](../diagram-index.md#d058)

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


**Definition 2C.1.** [Source](../source.tex#L3883); [PDF p. 10](../source.pdf#page=10).


The annular symmetric web category $\mathsf{AWeb}$ has the same objects as $\mathsf{Web}$ and morphisms given by $\mathcal A$-linear combinations of upward webs on a cylinder, modulo the local relations and isotopy with boundary fixed. The local relations also apply in disks meeting the cut. No Levi quotient is imposed. Write $\mathsf{AWeb}_N$ for the part of total thickness $N$.

A coil, displayed and defined by [Equation 2C.2](../paper.md#fig-cut-guide) for thin edges (similarly for arbitrary thickness), moves a boundary edge across the cut. Coils exist in both directions and at every thickness. On $\omega_N$, let $X_i$ be the positive winding at position $i$; its inverse has a negative sign. Suppressing strands,


<a id="fig-cut-guide"></a>


```latex
\begin{gather}
\text{[D059]}=\text{[D060]}
\quad\xleftrightarrow{\text{cut / glue}}\quad\text{[D061]},\quad
X_i=\text{[D062]},\qquad X_i^{-1}=\text{[D063]}.
\end{gather}
```

 [D059](../diagram-index.md#d059); [D060](../diagram-index.md#d060); [D061](../diagram-index.md#d061); [D062](../diagram-index.md#d062); [D063](../diagram-index.md#d063)


<a id="ai-statement-013"></a>


**Lemma 2C.3.** [Source](../source.tex#L3905); [PDF p. 10](../source.pdf#page=10).


We have


<a id="eq-invcoil"></a>


```latex
\begin{gather}
\text{[D064]}=\text{[D065]}=
\text{[D066]}.
\end{gather}
```

 [D064](../diagram-index.md#d064); [D065](../diagram-index.md#d065); [D066](../diagram-index.md#d066)


**Proof.**

A visualization exercise.

*End of proof.*


<a id="lem-annular-relations"></a>


**Lemma 2C.5.** [Source](../source.tex#L3923); [PDF p. 10](../source.pdf#page=10).


Adjoining coils to $\mathsf{Web}$ together with [Equation 2C.4](../paper.md#eq-invcoil) gives $\mathsf{AWeb}$. On a thin boundary, 

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

 [D067](../diagram-index.md#d067); [D068](../diagram-index.md#d068); [D069](../diagram-index.md#d069); [D070](../diagram-index.md#d070); [D071](../diagram-index.md#d071); [D072](../diagram-index.md#d072)

 Strands not involved in a relation remain fixed.

**Proof.**

The coil presentation is [[LTV23](../paper.md#bib-ltv), Section~4A]. The displayed relations follow by moving coils across the cut.

*End of proof.*

<a id="ai-statement-015"></a>


**Definition 2C.6.** [Source](../source.tex#L3948); [PDF p. 11](../source.pdf#page=11).


Let $\rho_N$ be the positive cyclic rotation of $\omega_N$ (cf. [Equation 2C.7](../paper.md#fig-rotation-in-webs)). Write $H_0$ for the crossing through the cut between the last and first thin positions. For $1\le a<N$, obtain $\beta_a$ from a reduced word for $w_a=[a+1,\ldots,N,1,\ldots,a]$ using positive thin crossings. A determinant dot on an $a$-edge denotes the product of its $a$ thin winding variables.

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

 [D073](../diagram-index.md#d073); [D074](../diagram-index.md#d074); [D075](../diagram-index.md#d075); [D076](../diagram-index.md#d076); [D077](../diagram-index.md#d077); [D078](../diagram-index.md#d078)

 The words are $\rho_3=X_1H_1H_2$ and $\rho_3^{-1}=H_2^{-1}H_1^{-1}X_1^{-1}$.


<a id="lem-boundary-rotation"></a>
<a id="subsec-affine-rotation"></a>


**Lemma 2C.8.** [Source](../source.tex#L3972); [PDF p. 11](../source.pdf#page=11).


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
\qquad\text{[D081]}=[2]\hspace{4pt}\text{[D082]}.$ [D079](../diagram-index.md#d079); [D080](../diagram-index.md#d080); [D081](../diagram-index.md#d081); [D082](../diagram-index.md#d082)

The thick dots are $X_1X_2$ and its inverse. A vertex meeting the cut is obtained by rotating its edges away from the cut, applying the ordinary vertex, and rotating back.

**Proof.**

Cutting open the rotation gives the braid and winding words. The product of winding variables passes through a split or merge, leaving the digon scalar $[2]$ in the last display.

*End of proof.*

<a id="ai-statement-017"></a>


**Remark 2C.10.** [Source](../source.tex#L4003); [PDF p. 11](../source.pdf#page=11).


Annular webs, also called affine webs and other names in the literature, have been studied in various settings; see, e.g., [[CK18](../paper.md#bib-ck), [FP14](../paper.md#bib-fominpylyavskyy), [LTV23](../paper.md#bib-ltv), [Que15](../paper.md#bib-queffelec), [SW25](../paper.md#bib-songwangwebs), [SSW25](../paper.md#bib-ssw)].


<a id="section-2d"></a>

### 2D. Hecke and Schur categories

<!-- Source: source.tex lines 4007; PDF page 12. -->


<a id="subsec-affine-local-maps"></a>


The following is a reinterpretation of, e.g., [[Lus89](../paper.md#bib-lusztigbernstein)], and many other sources.


<a id="def-affine-hecke-conventions"></a>


**Definition 2D.1.** [Source](../source.tex#L4011); [PDF p. 12](../source.pdf#page=12).


The extended affine symmetric group $\widehat S_N$ consists of bijections $w:\mathbb Z\to\mathbb Z$ with $w(i+N)=w(i)+N$. Its degree is $N^{-1}\sum_{i=1}^N(w(i)-i)$; the degree-zero subgroup is $W=\widetilde S_N$, and $W_0=\langle s_1,\ldots,s_{N-1}\rangle\cong S_N$. The rotation is $\tau=[2,3,\ldots,N,N+1]$.

The extended affine Hecke algebra $\mathcal H_{\rm aff}$ is the $\mathcal A$-algebra generated by $H_1,\ldots,H_{N-1}$ and $X_1^{\pm1},\ldots,X_N^{\pm1}$, subject to the braid, quadratic and Bernstein relations of [Lemma 2B.4](../paper.md#lem-thin-hecke-relations) and [Lemma 2C.5](../paper.md#lem-annular-relations), now read algebraically. Put 

```latex
\tau=X_1H_1\cdots H_{N-1},\qquad
H_0=\tau H_{N-1}\tau^{-1},\qquad
Q=v^{-2},\qquad H_i=vT_i.
```

 The $H_i$ with $1\le i<N$ generate the finite subalgebra $\mathcal H(W_0)$, and $(T_i+1)(T_i-Q)=0$. Write $H_w=v^{\ell(w)}T_w$ for the standard basis, with $T_\tau=\tau$. The degrees are $\deg H_i=0$ and $\deg X_i=\deg\tau=1$; the degree-zero subalgebra is the ordinary affine Hecke algebra.


<a id="def-spherical-modules"></a>


**Definition 2D.2.** [Source](../source.tex#L4039); [PDF p. 12](../source.pdf#page=12).


For a finite parabolic $P$ with longest element $w_P$, put 

```latex
x_P=\sum_{w\in P}T_w,\qquad
C_P=v^{\ell(w_P)}x_P,\qquad
h_P=v^{\ell(w_P)}\sum_{w\in P}Q^{\ell(w)}.
```

 The spherical right module is $\mathcal M_P=C_P\mathcal H_{\rm aff}=x_P\mathcal H_{\rm aff}$; its generator satisfies $C_PH_i=v^{-1}C_P$ for $s_i\in P$. For a composition $\gamma$, let $W_\gamma$ permute its consecutive blocks and write $\mathcal M_\gamma=\mathcal M_{W_\gamma}$, $x_\gamma=x_{W_\gamma}$ and $C_\gamma=C_{W_\gamma}$.


<a id="def-affine-schur-maps"></a>


**Definition 2D.3.** [Source](../source.tex#L4054); [PDF p. 12](../source.pdf#page=12).


The affine Schur category $\mathsf{Schur}_N$ has compositions of $N$ as objects and morphisms $\Hom_{\mathsf{Schur}_N}(\gamma,\alpha) =\Hom_{\mathcal H_{\rm aff}}(\mathcal M_\gamma,\mathcal M_\alpha),$ with composition of module maps.


<a id="lem-vertex-normalization"></a>


**Lemma 2D.4.** [Source](../source.tex#L4061); [PDF p. 12](../source.pdf#page=12).


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

 For adjacent edges $(a,b)$, take $P=S_{a+b}$ and $L=S_a\times S_b$; a vertex across the cut is transported by rotation as in [Lemma 2C.8](../paper.md#lem-boundary-rotation).

There is an algebra embedding, in fact an isomorphism, 

```latex
\begin{gather*}
\jmath_N:\mathcal H_{\rm aff}
\xrightarrow{\ \sim\ }\operatorname{End}_{\mathsf{AWeb}}(\omega_N).
\end{gather*}
```

 It sends $H_i$ to the thin crossing in positions $i,i+1$, $X_i^{\pm1}$ to the corresponding winding dot, and $\tau$ to $\rho_N$. Thus $H_{w_a}$ is represented by $\beta_a$. Its finite restriction is $\mathcal H(W_0)\cong\operatorname{End}_{\mathsf{Web}}(\omega_N)$.

**Proof.**

The isomorphism is [[SSW25](../paper.md#bib-ssw), Theorem~4.16, Proposition~4.18(1)], with $q=v$; see also [[Gre99](../paper.md#bib-greenaffine)], [[TVW17](../paper.md#bib-tvw), Theorem~3.22] and [[Bru25](../paper.md#bib-brundan)]. To fix the vertex normalization, let $P^L$ be the minimal right-coset representatives for $P/L$. Then 

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

 For adjacent edges this is exactly the digon scalar in [Equation 2B.2](../paper.md#eq-web-digon). These are the normalized maps of [[TVW17](../paper.md#bib-tvw), [LT26](../paper.md#bib-latifitubbenhauer)] and [[SSW25](../paper.md#bib-ssw), (3.21)--(3.22)]. The thin boundary has $\mathcal M_{\omega_N}=\mathcal H_{\rm aff}$. Since these are right modules, $h$ acts by left multiplication $L_h$, and $L_a\circ L_b=L_{ab}$. Apply [Equation 2D.5](../paper.md#eq-web-schur-hom); the finite case is analogous.

*End of proof.*

Henceforth we identify Schur maps with webs using $\Phi_N$. The algebraic degree is the signed, thickness-weighted-winding across the cut, so this identification also respects degree.


<a id="section-2e"></a>

### 2E. Standard and canonical bases

<!-- Source: source.tex lines 4127; PDF page 13. -->


We recall the standard and canonical bases of affine Schur maps, with the normalization needed below. Under the identification in [Lemma 2D.4](../paper.md#lem-vertex-normalization), the latter can be viewed as canonical annular webs.


<a id="def-hecke-kl-basis"></a>


**Definition 2E.1.** [Source](../source.tex#L4134); [PDF p. 13](../source.pdf#page=13).


The Hecke bar fixes $\tau$, sends $v$ to $v^{-1}$ and $H_i$ to $H_i^{-1}$. We use the KL normalization $C_w=v^{\ell(w)}\sum_{y\le w}P_{y,w}(v^{-2})T_y.$ In particular, $C_{w_P}=C_P$ and $C_{s_i}=H_i+v$. On Schur maps the induced bar is $\overline f(C_\gamma h)=\overline{f(C_\gamma)}h$.

Thus $C_{s_i}=b_i$ is the merge-split web of [Equation 2B.5](../paper.md#eq-thin-channel-normalization). Moreover, in pictures, 

```latex
\overline{\text{[D083]}}
=\text{[D084]},\qquad
\overline{\text{[D085]}}
=\text{[D086]},\qquad
\overline{\text{[D087]}}=\text{[D088]},\qquad
\overline{\rho_N}=\rho_N.
```

 [D083](../diagram-index.md#d083); [D084](../diagram-index.md#d084); [D085](../diagram-index.md#d085); [D086](../diagram-index.md#d086); [D087](../diagram-index.md#d087); [D088](../diagram-index.md#d088)


For thick crossings, the same rule reads $\overline{H_{a,b}}=H_{b,a}^{-1}$. For winding dots, [Equation 2C.9](../paper.md#eq-web-rotation) gives $\overline{X_1}=\rho_N H_{N-1}\cdots H_1$. For example, on three thin strands,

$\displaystyle
\overline{\text{[D089]}}
=\text{[D090]}.$ [D089](../diagram-index.md#d089); [D090](../diagram-index.md#d090)

The other positions and inverse dots follow from the annular relations.


<a id="def-schur-bases"></a>


**Definition 2E.2.** [Source](../source.tex#L4169); [PDF p. 13](../source.pdf#page=13).


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


**Lemma 2E.3.** [Source](../source.tex#L4201); [PDF p. 13](../source.pdf#page=13).


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

The degree formula is [[DF15](../paper.md#bib-dufu), (2.0.3)] with parameter $v^{-1}$, or [[Cui14](../paper.md#bib-cui), Lemma~7.2] with $t=v^{-1}$. Grouping the KL expansion into double cosets gives the change of basis and triangularity [[Cui14](../paper.md#bib-cui), Lemma~3.1, Theorem~3.1, (3.4)--(3.5)]. Bar invariance follows from that of $C_{w_A^+}$.

*End of proof.*

There is also a diagrammatic description of the standard basis. Write $\iota_{\gamma,\omega_N}$ and $\mu_{\omega_N,\alpha}$ for the total split and merge, and put $I_A=W_\alpha\cap d(A)W_\gamma d(A)^{-1}$. Then 

```latex
h_{I_A}[A]_v
=\mu_{\omega_N,\alpha}\circ\jmath_N(H_{d(A)})
\circ\iota_{\gamma,\omega_N}
=\text{[D091]}.
```

 [D091](../diagram-index.md#d091)

 This is a diagrammatic sandwich, in the spirit of sandwich cellularity as in, e.g., [[Tub24](../paper.md#bib-sandwich)]. Indeed, parabolic multiplication gives 

```latex
C_\alpha H_{d(A)}C_\gamma
=h_{I_A}\,v^{\ell(w_A^+)}
\sum_{w\in W_\alpha d(A)W_\gamma}T_w,
```

 and the two sides define the same map on $C_\gamma$. The factor $h_{I_A}$ accounts for repeated symmetrization at the overlap. Canonical webs are bar invariant triangular combinations of these standard webs; they need not be single diagrams.

<a id="ai-statement-025"></a>


**Remark 2E.5.** [Source](../source.tex#L4268); [PDF p. 14](../source.pdf#page=14).


These bases come from [[BLM90](../paper.md#bib-blm), [Du92](../paper.md#bib-du), [Lus99](../paper.md#bib-lusztigaffine)], in the induced-trivial convention of [[Deo87](../paper.md#bib-deodhar)]; see also [[McG03](../paper.md#bib-mcgerty)] for a useful summary. They differ from the elementary ribbon basis of [[SSW25](../paper.md#bib-ssw), Theorem~4.16]: a composite web must be expanded in the standard basis before one can read its KL coefficients. An analogous distinction appears in the classical web calculus: Khovanov--Kuperberg (KK) showed that the $\mathfrak{sl}_3$ web basis is not in general dual canonical [[KK99](../paper.md#bib-kk99)].

<a id="ai-statement-026"></a>


**Example 2E.6.** [Source](../source.tex#L4279); [PDF p. 14](../source.pdf#page=14).


Already on three thin strands, a composite web can require a canonical correction: 

```latex
\underbrace{\text{[D092]}}_{b_1b_2b_1}
-\underbrace{\text{[D093]}}_{b_1}
=\underbrace{\text{[D094]}}_{C_{s_1s_2s_1}}.
```

 [D092](../diagram-index.md#d092); [D093](../diagram-index.md#d093); [D094](../diagram-index.md#d094)

 Indeed, expanding $b_i=H_i+v$ and applying the quadratic relation gives 

```latex
b_1b_2b_1-b_1
=H_{s_1s_2s_1}+v(H_{s_1s_2}+H_{s_2s_1})
 +v^2(H_{s_1}+H_{s_2})+v^3=C_{S_3}.
```

 The final web is the total merge followed by the total split, which represents $C_{S_3}$ by [Lemma 2D.4](../paper.md#lem-vertex-normalization). Thus even a bar invariant composite need not itself be canonical.


<a id="def-dictionary-corner"></a>


**Definition 2E.7.** [Source](../source.tex#L4299); [PDF p. 14](../source.pdf#page=14).


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


**Lemma 2E.8.** [Source](../source.tex#L4326); [PDF p. 14](../source.pdf#page=14).


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

 [D095](../diagram-index.md#d095)


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


**Proposition 2E.10.** [Source](../source.tex#L4389); [PDF p. 15](../source.pdf#page=15).


The required affine KL coefficient is read from the canonical web by 

```latex
\big[[B_m]_v\big]\theta_{A_{j;m}}
=v^{D_{j;m}}P_{w_0,uw_0}(v^{-2}).
```

 In particular, $[v]\big(\big[[B_m]_v\big]\theta_{A_{j;m}}\big)=\mu_{j;m}.$

**Proof.**

Apply [Equation 2E.4](../paper.md#eq-exact-schur-dictionary) with $Z=B_m$. Since $D_{j;m}$ is odd, the term of degree $(D_{j;m}-1)/2$ in the KL polynomial becomes the coefficient of $v$.

*End of proof.*

As we will see in [Section 3](../paper.md#sec-algebraic-gallery), the standard coefficients of our main web are straightforward to compute, leaving only the base change to the canonical basis (which we carry out in [Section 4](../paper.md#sec-algebraic-relevance)). Afterwards, [Proposition 2E.10](../paper.md#cor-dictionary-readout) directly yields the required coefficient.


