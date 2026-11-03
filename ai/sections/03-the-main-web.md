# 3. The main web

Part of *Annular webs and Guralnick's conjecture*, snapshot 2026-11-03. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.

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

 [D096](../diagram-index.md#d096); [D097](../diagram-index.md#d097); [D098](../diagram-index.md#d098); [D099](../diagram-index.md#d099); [D100](../diagram-index.md#d100); [D101](../diagram-index.md#d101)


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

 [D102](../diagram-index.md#d102)

 The blue unit strands exposed in (c) pass unchanged through (d)--(e) and rejoin in (f).


<a id="section-3b"></a>

### 3B. The symmetrizer expression

<!-- Source: source.tex lines 4462; PDF page 16. -->


By [Lemma 2D.4](../paper.md#lem-vertex-normalization), a split $P\to Q$, $Q\subset P$, is the inclusion $M_P\to M_Q$; the reverse merge sends $C_Qh$ to $C_Ph$. Thus (a)--(f) give the parabolic chain $W_0\supset V\subset J\supset L\subset K\supset L\subset V$, where $W_0=\langle s_1,\ldots,s_{N-1}\rangle$ and 

```latex
\begin{aligned}
J&=\langle s_i:i\in\mathbb Z/N\mathbb Z
\setminus\{m,m+1\}\rangle,
& K&=\langle s_2,\ldots,s_{N-2}\rangle,\\
V&=W_0\cap J,
& L&=J\cap K=K\cap V.
\end{aligned}
```

 Their types are $V\cong S_m\times S_m$, $J\cong S_{2m}$, $K\cong S_{2m-1}$ and $L\cong S_{m-1}\times S_{m-1}$. The $2m$-edge of $J=(2m,1)$ crosses the cut, so $J$ contains $s_0$ but is finite, with symmetrizer $C_J=\tau^{m+1}C_{\langle s_1,\ldots,s_{N-2}\rangle}\tau^{-(m+1)}$. By [Lemma 2C.8](../paper.md#lem-boundary-rotation), (b)--(c) are ordinary parabolic maps transported across the cut, hence integral of degree zero.


<a id="lem-main-symmetrizer"></a>


**Lemma 3B.1.** [Source](../source.tex#L4486); [PDF p. 16](../source.pdf#page=16).


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

Evaluate the six maps of [Section 3A](../paper.md#s-mainweb) on $C_{W_0}$ using [Lemma 2D.4](../paper.md#lem-vertex-normalization). Over $\mathbb Q(v)$, their composite is $C_VC_KC_JC_{W_0}/(h_Vh_L^2)$. The overlaps $W_0\cap J=V$, $J\cap K=L$ and $K\cap V=L$ give the three digon factors. Thus the quotient represents the six integral maps, and inversion reverses the product as stated. Every $C_P$ and $h_P$ is bar invariant.

*End of proof.*

<a id="ai-statement-031"></a>


**Remark 3B.3.** [Source](../source.tex#L4507); [PDF p. 17](../source.pdf#page=17).


The use of parabolic chains is classical in the Schur algebroid; see [[Wil11](../paper.md#bib-williamson)]. Elias--Ko relate this combinatorics to ordinary type $A$ webs via an associated graded construction [[EK23](../paper.md#bib-eliasko)]. For products of parabolic KL elements and their canonical corrections, see also [[AS21](../paper.md#bib-agrawalsotirov)].

Write $C_A,\Delta_A$ for the images of $\theta_A,[A]_v$ under $H_w^*=H_{w^{-1}}$. Then $C_B=M_e$ and $[\Delta_A]C_Z=[[A]_v]\theta_Z$. Indeed, 

```latex
[A]_v(C_{W_0})=v^{\ell(w_A^+)}
\sum_{w\in Vd(A)W_0}T_w,
```

 and $*$ replaces this coset by $W_0d(A)^{-1}V$ without changing the scalar. The anti-involution $*$ sends $H_w$ to $H_{w^{-1}}$ and reverses products. The bar sends $H_w$ to $H_{w^{-1}}^{-1}$, sends $v$ to $v^{-1}$, and preserves products.


<a id="section-3c"></a>

### 3C. Counting flags

<!-- Source: source.tex lines 4529; PDF page 17. -->


Schur convolution counts intermediate flags [[BLM90](../paper.md#bib-blm), [Lus99](../paper.md#bib-lusztigaffine)]. For $\mathcal R_m$, we choose a line, a hyperplane and an $m$-space inside an $(m+1)$-space in an $N$-dimensional quotient.


<a id="def-gallery-flags"></a>


**Definition 3C.1.** [Source](../source.tex#L4535); [PDF p. 17](../source.pdf#page=17).


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


**Lemma 3C.3.** [Source](../source.tex#L4585); [PDF p. 17](../source.pdf#page=17).


Over $\mathbb F_Q$, the number of galleries is $F_A(Q)$.

**Proof.**

The $\mathsf L_\epsilon$ choices of $L$ and $\mathsf H_\eta$ choices of $H$ are independent since $L\subset F\subset F'\subset H$. The remaining flag $I_0+L\subset I\subset K\subset K_0\cap H$ has endpoint dimensions $r+\epsilon$ and $N-r-\eta$: 

```latex
\text{[D103]}
```

 [D103](../diagram-index.md#d103)


Choose $I/(I_0+L)$ in the quotient of dimension $N-2r-\epsilon-\eta$, then the line $K/I$. These give the Gaussian and quantum-integer factors in [Equation 3C.2](../paper.md#eq-gallery-gaussian).

*End of proof.*

The same count has a local web calculation. Put $n=N-2r-\epsilon-\eta$ and $k=m-r-\epsilon$ in a feasible case. The quotient flag has dimensions $k,k+1$ in dimension $n$. Choosing the $(k+1)$-space first gives the left web; choosing the $k$-space first gives the right web: 

```latex
\text{[D104]}
=\text{[D105]}
=\genfrac{[}{]}{0pt}{}{n}{k}[n-k]\,\text{[D106]}.
```

 [D104](../diagram-index.md#d104); [D105](../diagram-index.md#d105); [D106](../diagram-index.md#d106)

 The first equality is associativity and coassociativity; the second removes the two digons. Write $\langle W\rangle$ for the scalar multiplying the straight strand in such an ordinary split--merge web $W$. This is an open-web evaluation, not a trace. Multiplying the displayed scalar by $v^{-k(n-k)-(n-k-1)}$ gives $\genfrac{[}{]}{0pt}{}{n}{k}_Q[n-k]_Q$, exactly the two remaining factors in [Equation 3C.2](../paper.md#eq-gallery-gaussian). Delete a zero edge at $k=0$ or $k=n-1$; infeasible cases contribute zero.


<a id="prop-gallery-standard"></a>


**Proposition 3C.4.** [Source](../source.tex#L4635); [PDF p. 18](../source.pdf#page=18).


Put $D=2m^2+2m-3$. The standard coefficient of $\mathcal R_m$ is 

```latex
\big[[A]_v\big]\mathcal R_m=v^{D-d_A}F_A(v^{-2}).
```

 All standards outside the support of [Definition 3C.1](../paper.md#def-gallery-flags) vanish. At the source $B=B_m$,


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

 [D107](../diagram-index.md#d107)

 The endpoint lattices have equal determinant degree, so $\dim(\widetilde I/\Lambda')=m$ and $\dim(\widetilde K/\Lambda')=m+1$. Refining the common facets to complete chambers introduces their Poincaré factors $h_V,h_L,h_L$; forgetting these refinements cancels the denominator in [Equation 3B.2](../paper.md#eq-marked-symmetrizer).

The inclusions force $\Lambda\subset t^{-1}\Lambda'$ and $\Lambda'\subset t^{-1}\Lambda$. Hence the relative exponents are $-1,0,1$, with $r$ of each nonzero sign, proving the support assertion. In $E=t^{-1}\Lambda'/\Lambda'$, set 

```latex
I_0=(\Lambda+\Lambda')/\Lambda',\qquad
K_0=(t^{-1}\Lambda\cap t^{-1}\Lambda')/\Lambda',\qquad
(F,F')=(\widetilde F,\widetilde F')/\Lambda'.
```


The quotient has the dimensions and intersections of [Definition 3C.1](../paper.md#def-gallery-flags), and its galleries are counted by $F_A(Q)$. The count over all finite fields gives the polynomial identity for Hecke multiplication.

For $\ell_P=\ell(w_P)$, we have $\ell_J=m(2m-1)$, $\ell_K=(2m-1)(m-1)$, $\ell_V=m(m-1)$ and $\ell_L=(m-1)(m-2)$. The normalization exponent is therefore $\ell_J+\ell_K+\ell_V-\ell_V-2\ell_L=D$; the output standard removes $d_A$. At $B$, $r=a=b=0$, $c=m$, $d=m+1$, and only $(\epsilon,\eta)=(1,1)$ contributes, giving [Equation 3C.5](../paper.md#eq-gallery-source). At $A_{m;m}$ the intermediate flags are forced, so $F_A=1$ and $d_A=D$.

*End of proof.*

Each individual choice is likewise a digon scalar. For $d\ge1$ and $0\le k\le n$, 

```latex
[d]_Q=v^{1-d}\left\langle\,\text{[D108]}\,\right\rangle,\qquad
\genfrac{[}{]}{0pt}{}{n}{k}_Q=v^{-k(n-k)}\left\langle\,\text{[D109]}\,\right\rangle.
```

 [D108](../diagram-index.md#d108); [D109](../diagram-index.md#d109)

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

 [D110](../diagram-index.md#d110); [D111](../diagram-index.md#d111); [D112](../diagram-index.md#d112); [D113](../diagram-index.md#d113)


For $m=2$ this is $v^4(v+v^{-1})^3(v^2+1+v^{-2})$, giving $2^3\cdot3=24$ at $v=1$. [Section 5](../paper.md#sec-aggregate-calibration) expands and corrects this product.


