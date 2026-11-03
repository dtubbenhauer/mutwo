# 5. The first example in pictures

Part of *Annular webs and Guralnick's conjecture*, snapshot 2026-11-03. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.

<a id="section-5"></a>

## 5. The first example in pictures

<!-- Source: source.tex lines 5656; PDF page 29. -->


<a id="sec-aggregate-calibration"></a>


For $m=2$, the boundary is $(5)\to(2,1,2)$ and the intermediate refinement is thin. Removing the four smaller canonical summands recovers $\mu_{2;2}=2$ from [[SX10](../paper.md#bib-sx), Lemma~3.4].


<a id="section-5a"></a>

### 5A. Constructing and expanding the web

<!-- Source: source.tex lines 5662; PDF page 29. -->


The completed webs $\mathcal R_2:(5)\to(2,1,2)$ and $\mathcal R_3:(7)\to(3,1,3)$ appear in [Figure 3](../paper.md#fig-intro-affine-construction); their interior labels are in [Equation 3A.1](../paper.md#fig-continuous-m2). Here are all six stages for $m=2$. Each composite has input $5$; the blue strands bypass the middle merge and split, then rejoin at (f): 

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

 [D170](../diagram-index.md#d170); [D171](../diagram-index.md#d171); [D172](../diagram-index.md#d172); [D173](../diagram-index.md#d173); [D174](../diagram-index.md#d174); [D175](../diagram-index.md#d175)


<a id="lem-seed-expansion"></a>


**Lemma 5A.1.** [Source](../source.tex#L5681); [PDF p. 29](../source.pdf#page=29).


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

The classification leaves these five terms. The family multiplicities are one by [Lemma 4I.1](../paper.md#lem-all-two-mark-multiplicities); the one-line multiplicities are constant with leading coefficient one. Finally, $g_2=v+v^{-1}$.

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

 [D176](../diagram-index.md#d176); [D177](../diagram-index.md#d177); [D178](../diagram-index.md#d178); [D179](../diagram-index.md#d179)


Removing the source term gives $\mathcal R_2^{\rm crit}=\mathcal R_2-(v+v^{-1})B_2$, as drawn in [Figure 5](../paper.md#fig-intro-critical-correction). To isolate $\theta_{A_{2;2}}$, we also need the smaller family term.


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

 [D180](../diagram-index.md#d180); [D181](../diagram-index.md#d181)


<a id="section-5c"></a>

### 5C. Reading the coefficient

<!-- Source: source.tex lines 5746; PDF page 30. -->


Substitution cancels the source terms in [Equation 5A.2](../paper.md#eq-seed-aggregate-identity): $\theta_{A_{2;2}}=\mathcal R_2-\mathcal U_2
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

 [D182](../diagram-index.md#d182); [D183](../diagram-index.md#d183); [D184](../diagram-index.md#d184); [D185](../diagram-index.md#d185)


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


