# 4. The base change (main calculation)

Part of *Annular webs and Guralnick's conjecture*, snapshot 2026-11-03. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.

<a id="section-4"></a>

## 4. The base change (main calculation)

<!-- Source: source.tex lines 4743; PDF page 19. -->


<a id="sec-algebraic-relevance"></a>


The following section is the main calculation, which is a bit tedious, though not difficult. The reader might want to skip to [Section 6](../paper.md#sec-guralnick) for the conclusion, or to [Section 5](../paper.md#sec-aggregate-calibration) for an example.


<a id="section-4a"></a>

### 4A. Parameters and degrees

<!-- Source: source.tex lines 4748; PDF page 19. -->


Degrees of flag counts restrict the canonical support to six families and the multiplicities of $A_{j;m}$ to zero or one.


<a id="def-relevance-parameters"></a>


**Definition 4A.1.** [Source](../source.tex#L4753); [PDF p. 19](../source.pdf#page=19).


Write $r=m-\ell$, with $0\le r\le m$. Every matrix in the support of [Proposition 3C.4](../paper.md#prop-gallery-standard) has the form 

```latex
\begin{gather*}
A=\begin{pmatrix}
a&\ell+s-a&r-s\\
\beta&\delta-\beta&1-\delta\\
r-a-\beta&\ell+1-s-\delta+a+\beta&s+\delta-1
\end{pmatrix},\qquad a_{i+3,j+3}=a_{ij}.
\end{gather*}
```

 All entries are nonnegative. Thus $(\beta,\delta)\in\{(0,0),(0,1),(1,1)\}$, and $s\ge1$ if $\delta=0$. The intersection dimensions from [Definition 3C.1](../paper.md#def-gallery-flags) are $b=a+\beta$, $c=\ell+s$ and $d=\ell+s+\delta$; put $z=s+\delta-1$.


<a id="lem-gallery-degrees"></a>


**Lemma 4A.2.** [Source](../source.tex#L4769); [PDF p. 19](../source.pdf#page=19).


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

Substitute the intersection dimensions into [Equation 3C.2](../paper.md#eq-gallery-gaussian). Since $c\ge a$ and $\ell+b\ge z$, the differences of quantum integers are nonnegative. In the length sum of [Definition 2E.2](../paper.md#def-schur-bases), only two row periods contribute: the predecessor gives $r^2$, the product of the outer column sums, and the current period gives 

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


**Lemma 4B.1.** [Source](../source.tex#L4811); [PDF p. 19](../source.pdf#page=19).


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

For $\mathcal R_m=\sum_A M_A(v)C_A$, integrality and bar invariance give $M_A\in\mathbb Z[v,v^{-1}]$ and $M_A(v)=M_A(v^{-1})$. Moreover, $d_mM_A\in\mathbb N[v,v^{-1}]$: the cleared product embeds as $C_{W_0}C_JC_KC_V$, whose KL coefficients and structure constants are positive [[KL80](../paper.md#bib-kl80), [Spr82](../paper.md#bib-springer82)]. The embedding preserves canonical normalization: for a minimal left-coset representative $x$, $C_{W_0}H_x$ has leading term $H_{w_{W_0}x}$, so its bar invariant triangular correction is $C_{w_{W_0}x}$. Grouping right $V$-cosets keeps leading coefficient one.

[Lemma 4B.1](../paper.md#lem-undivided-positivity-degree) and [Proposition 3C.4](../paper.md#prop-gallery-standard) now give


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


**Definition 4C.1.** [Source](../source.tex#L4861); [PDF p. 20](../source.pdf#page=20).


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

 [D114](../diagram-index.md#d114); [D115](../diagram-index.md#d115); [D116](../diagram-index.md#d116); [D117](../diagram-index.md#d117); [D118](../diagram-index.md#d118); [D119](../diagram-index.md#d119)


<a id="prop-algebraic-six"></a>


**Lemma 4C.2.** [Source](../source.tex#L4895); [PDF p. 20](../source.pdf#page=20).


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

Put $f_0=\ell^2+2\ell-3$. The four nonempty terms of [Equation 4A.3](../paper.md#eq-relevance-four-terms) have degrees $f_0$ plus $2a+\beta$, $a+s+\beta$, $a+s+\delta$, $2s+\delta-1$. By [Equation 4B.2](../paper.md#eq-relevance-bound), their maximum must give $E\ge0$. There are three possible middle rows.

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

In family $\mathrm F$, the unique top-degree term is $[\ell+1]_q\genfrac{[}{]}{0pt}{}{2\ell+1}{\ell}_q$, monic; at $\ell=0$, $F_A=1$. Hence $[\Delta_A]\mathcal R_m$ has valuation zero and constant one, so $M_A$ is constant. Since $d_mM_A$ is nonnegative and $d_m$ has lowest coefficient one, the positive identity above [Equation 4B.2](../paper.md#eq-relevance-bound) gives $0\le M_A\le1$. The family $\mathrm F$ matrix is 

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


**Lemma 4D.1.** [Source](../source.tex#L4989); [PDF p. 21](../source.pdf#page=21).


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


**Definition 4E.1.** [Source](../source.tex#L5012); [PDF p. 21](../source.pdf#page=21).


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

 [D120](../diagram-index.md#d120); [D121](../diagram-index.md#d121)

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

 [D122](../diagram-index.md#d122); [D123](../diagram-index.md#d123); [D124](../diagram-index.md#d124); [D125](../diagram-index.md#d125)

 All inner inputs have label $5$; (b) merges the entire edge.


<a id="prop-full-gaussian-algebraic"></a>


**Lemma 4E.2.** [Source](../source.tex#L5042); [PDF p. 22](../source.pdf#page=22).


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

Apply [Lemma 4B.1](../paper.md#lem-undivided-positivity-degree) with $d=h_{I_s}^2$; clearing $d$ gives a positive product of canonical symmetrizers. The standard coefficients have valuation zero and constant one, so the degree bound and bar symmetry make all multiplicities constant. Descending through ranks, larger canonical terms have positive degree at smaller standards. The constant term therefore gives each multiplicity as one.

*End of proof.*

Put $h=s-r$ and $n=N-2r$. Since $2s(N-s)-2r(N-r)=2h(n-h)$, the coefficient is

$\displaystyle
\big[[Z_r]_v\big]\mathcal V_s
=v^{h(n-h)}\left\langle\,\text{[D126]}\,\right\rangle.$ [D126](../diagram-index.md#d126)

The digon has extreme degrees $\pm h(n-h)$ with coefficients one, hence valuation zero and constant one after shifting.


<a id="cor-spherical-differences"></a>


**Lemma 4E.4.** [Source](../source.tex#L5089); [PDF p. 22](../source.pdf#page=22).


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

Subtract the canonical expansions in [Lemma 4E.2](../paper.md#prop-full-gaussian-algebraic), then the coefficients in [Equation 4E.3](../paper.md#eq-full-raw-coefficient). Their normalization exponents differ by $2(N-2s+1)=2(n-2h+1)$, giving the power of $Q$. The case $s=0$ is immediate.

*End of proof.*

Write $K_{\alpha,\beta}(t)$ for the Kostka--Foulkes transition polynomial from Schur to Hall--Littlewood functions. Gaussian reciprocity with $t=v^2$ rewrites [Equation 4E.5](../paper.md#eq-full-canonical-coefficient) as 

```latex
\big[[Z_r]_v\big]C_{Z_s}
=\genfrac{[}{]}{0pt}{}{n}{h}_t-\genfrac{[}{]}{0pt}{}{n}{h-1}_t
=K_{(2^h,1^{n-2h}),(1^n)}(t).
```

 Here a Gaussian with lower index $-1$ is zero. The last equality is the two-column case of Macdonald's hook formula [[Mac95](../paper.md#bib-macdonald), Chapter~III, Section~6, Example~2]. This spherical affine KL interpretation goes back to Lusztig [[Lus83](../paper.md#bib-lusztigspherical)] and Kato [[Kat82](../paper.md#bib-kato)]; [[NR03](../paper.md#bib-nelsenram), Theorem~3.4(d)] gives an explicit account of the inverse parameter convention. This gives the full-spherical correction in our three-output calculation. In the web calculus, for $h\ge1$ the same coordinate is 

```latex
[[Z_r]_v]C_{Z_s}
=v^{h(n-h)}\left\langle\,\text{[D127]}\,\right\rangle
-v^{(h-1)(n-h+1)}\left\langle\,\text{[D128]}\,\right\rangle.
```

 [D127](../diagram-index.md#d127); [D128](../diagram-index.md#d128)

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

 [D129](../diagram-index.md#d129); [D130](../diagram-index.md#d130); [D131](../diagram-index.md#d131); [D132](../diagram-index.md#d132); [D133](../diagram-index.md#d133); [D134](../diagram-index.md#d134); [D135](../diagram-index.md#d135); [D136](../diagram-index.md#d136)

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
Appending the splitter of [Equation 2E.9](../paper.md#fig-spherical-boundary) gives
\end{minipage}\qquad
C_{Z_r}=\text{[D137]}-\text{[D138]}
\qquad(r\ge1).
\end{gather}
```

 [D137](../diagram-index.md#d137); [D138](../diagram-index.md#d138)

 At rank zero the refined canonical web is the ordinary splitter $B_m$.


<a id="section-4f"></a>

### 4F. One retained line

<!-- Source: source.tex lines 5169; PDF page 24. -->


We need the following.


<a id="def-one-line-web"></a>


**Definition 4F.1.** [Source](../source.tex#L5173); [PDF p. 24](../source.pdf#page=24).


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

 [D139](../diagram-index.md#d139); [D140](../diagram-index.md#d140)

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

 [D141](../diagram-index.md#d141); [D142](../diagram-index.md#d142); [D143](../diagram-index.md#d143); [D144](../diagram-index.md#d144)

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


**Lemma 4F.2.** [Source](../source.tex#L5220); [PDF p. 24](../source.pdf#page=24).


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

 [D145](../diagram-index.md#d145); [D146](../diagram-index.md#d146); [D147](../diagram-index.md#d147)

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

 [D148](../diagram-index.md#d148); [D149](../diagram-index.md#d149)


For $N=7$, $j=2$, split the right $4$-edge of $\mathcal E_{2,3}$ or the left $4$-edge of $\mathcal E_{2,4}$. Both retain the blue line and end at $(3,1,3)$:


```latex
\begin{gather*}
\begin{array}{c@{\qquad}c}
\text{[D150]}\circ\text{[D151]}=\text{[D152]}&
\text{[D153]}\circ\text{[D154]}=\text{[D155]}
\end{array}
\end{gather*}
```

 [D150](../diagram-index.md#d150); [D151](../diagram-index.md#d151); [D152](../diagram-index.md#d152); [D153](../diagram-index.md#d153); [D154](../diagram-index.md#d154); [D155](../diagram-index.md#d155)


<a id="section-4h"></a>

### 4H. The one-line degree bound

<!-- Source: source.tex lines 5312; PDF page 25. -->


Set $N=2m+1$. The image families have $f=m$ or $m+1$ for strong or weak incidence; reflection gives the kernel families. By [Equation 4D.2](../paper.md#eq-parabolic-refinement), output refinement to $(m,1,m)$ preserves their canonical vectors.


<a id="cor-one-mark-margin"></a>


**Lemma 4H.1.** [Source](../source.tex#L5319); [PDF p. 25](../source.pdf#page=25).


Let a one-line canonical term have rank $s$, and put $l'=m-s$. At a full-spherical standard of rank $r<s$, its minimum degree is $l'+2$ for the strong family and $l'+1$ for the weak family. After multiplying by its coefficient in $\mathcal R_m$, the minimum degree is at least three in either case. The same holds for the dual families.

**Proof.**

At this standard $a=0,c=f-r$, so the polynomial in [Equation 4F.3](../paper.md#eq-one-mark-coefficient) is $[f-r]_Q\genfrac{[}{]}{0pt}{}{N-2r-1}{s-r-1}_Q$. Subtracting twice its degree from the length gap gives $N-s-f+1$. The relevance bounds allow multiplicity degrees down to $-(l'-1)$ and $-(l'-2)$ respectively. Both resulting margins are three. For $s\le r$ the coefficient vanishes.

*End of proof.*

Diagrammatically, the margins are

$\displaystyle\begin{array}{c@{\qquad}c}
\text{[D156]}&\text{[D157]}\\[1ex]
\text{strong: }(l'+2)-(l'-1)=3&
\text{weak: }(l'+1)-(l'-2)=3
\end{array}$ [D156](../diagram-index.md#d156); [D157](../diagram-index.md#d157)

Reflection gives the other two cases.


<a id="section-4i"></a>

### 4I. Multiplicity one

<!-- Source: source.tex lines 5354; PDF page 26. -->


<a id="sec-multiplicity-one"></a>


We now control the multiplicity.


<a id="lem-all-two-mark-multiplicities"></a>


**Lemma 4I.1.** [Source](../source.tex#L5358); [PDF p. 26](../source.pdf#page=26).


Every family $\mathrm F$ index has multiplicity $M_{A_{j;m}}=1$ for $1\le j\le m$.

**Proof.**

Fix $j$ and an auxiliary rank $s\ge j$. Put $h=s-j$, $k=m-j$ and $\ell=m-s=k-h$. Full-spherical refinement to $A_{j;m}$ contributes the factor $v^{2k+3}$. Its canonical coefficient has nonnegative valuation and its multiplicity has valuation at least $-(2\ell-3)$, so the total valuation is at least $(2k+3)-(2\ell-3)=2h+6$.

For a strong one-line term (mark dimension $f=m$), the relative parameters in [Equation 4F.3](../paper.md#eq-one-mark-coefficient) are $n=2k+1$, $a=b=1$, $c=k+1$, $d=k$. For the weak term ($f=m+1$), only $c,d$ change, to $k+2,k+1$. The codimension statistic for either two-row matrix is $2k+2$; refinement to the three-row matrix therefore adds one more power of $v$. Their counting polynomials are, respectively, 

```latex
\genfrac{[}{]}{0pt}{}{n}{h}_Q+([k+1]_Q-1)\genfrac{[}{]}{0pt}{}{n-1}{h-1}_Q,
\qquad
\genfrac{[}{]}{0pt}{}{n}{h}_Q+([k+2]_Q-1)\genfrac{[}{]}{0pt}{}{n-1}{h-1}_Q.
```

 The first Gaussian has degree $h(n-h)$. The second is lower by $\ell+1$ or $\ell$, respectively, and absent at $h=0$. Here $\ell\ge1$ by [Lemma 4C.2](../paper.md#prop-algebraic-six). Subtracting twice the degree from the refined length gap gives valuations $\ell+2h+1$, $\ell+2h+2$. The multiplicity bounds $-(\ell-1)$, $-(\ell-2)$ leave total valuations at least $2h+2$, $2h+4$, respectively. Reflection gives the same bounds for the kernel families; the auxiliary canonical coefficients vanish at rank $j>s$.

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


**Lemma 4J.1.** [Source](../source.tex#L5429); [PDF p. 26](../source.pdf#page=26).


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

 Here $\genfrac{[}{]}{0pt}{}{2m+1}{r}_q\equiv1/(q;q)_r\pmod{q^m}$ for $0\le r\le m-1$. Euler's partition identity $\sum_{r\ge0}q^r/(q;q)_r=1/(q;q)_\infty$ finishes the proof [[Mac95](../paper.md#bib-macdonald), Chapter~I, Section~2, Example~4].

*End of proof.*


<a id="lem-gaussian-cancellation"></a>


**Lemma 4J.2.** [Source](../source.tex#L5462); [PDF p. 27](../source.pdf#page=27).


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

 Every reversed term is a polynomial, and $Y_m$ is reciprocal. We compute the reversal of $Q_m$ modulo $q^m$. In [Lemma 4J.1](../paper.md#lem-gaussian-truncation), $\Delta_0(0)=1$ and $\Delta_r(0)=0$ for $r>0$. Including the $H_1$, the lemma gives 

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


**Lemma 4K.1.** [Source](../source.tex#L5504); [PDF p. 27](../source.pdf#page=27).


The coefficient of $C_{Z_r}$ in $\mathcal R_m$ is $g_{m-r}(v)$ for $0\le r\le m-2$; no full-spherical term of rank $m-1$ occurs. The integral bar invariant web 

```latex
\begin{gather*}
\mathcal R_m^{\mathrm{crit}}
=\mathcal R_m-\sum_{r=0}^{m-2}g_{m-r}(v)C_{Z_r}
\end{gather*}
```

 has at $B$ valuation at least one and coefficient $\binom{m+1}{2}$ at $v$.

**Proof.**

Descend through the spherical ranks. At $Z_r$, put $l=m-r$. The raw coordinate is $v^{D_l}Y_l(v^{-2})$, and the coordinate of $C_{Z_{r+h}}$ is $v^{2h(2l+1-h)}R_{2l+1,h}(v^{-2})$. The one-line contributions have valuation at least three by [Lemma 4H.1](../paper.md#cor-one-mark-margin). The family $\mathrm F$ multiplicities are constant, and their coefficients here are proper canonical coefficients, hence have positive degree. Thus only spherical terms affect the nonpositive part.

The classification excludes $l=1$. Suppose the multiplicities at larger ranks are known. Since $D_l-D_{l-h}=2h(2l+1-h)$, subtracting those terms and the proposed $g_lC_{Z_r}$ leaves, at $Z_r$, $v^{D_l}Q_l(v^{-2})\in v\mathbb Z[v]$ by [Lemma 4J.2](../paper.md#lem-gaussian-cancellation). Hence $M_{Z_r}-g_l\in v\mathbb Z[v]$. This difference is bar invariant, so it is zero. At $r=0$, the same lemma gives valuation at least one and coefficient $\binom{m+1}{2}$ at $v$.

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

 [D158](../diagram-index.md#d158); [D159](../diagram-index.md#d159); [D160](../diagram-index.md#d160)


All terms have boundary $(N)\to(m,1,m)$; the sum is empty for $m=2$. Using [Equation 4E.6](../paper.md#eq-refined-spherical-picture), the first corrections are 

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

 [D161](../diagram-index.md#d161); [D162](../diagram-index.md#d162); [D163](../diagram-index.md#d163)

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

 [D164](../diagram-index.md#d164)

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

 [D165](../diagram-index.md#d165); [D166](../diagram-index.md#d166); [D167](../diagram-index.md#d167); [D168](../diagram-index.md#d168)


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


**Theorem 4L.1.** [Source](../source.tex#L5604); [PDF p. 28](../source.pdf#page=28).


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

 The last sum has minimum degree at least three at $B$. Taking $[v]$ and using the canonical-to-standard dictionary gives [Equation 4L.2](../paper.md#eq-aggregate-web-theorem). Its consequence follows by averaging and integrality.

*End of proof.*

The sum $S_m=\sum_j\mu_{j;m}=\binom{m+1}{2}$ also counts triples of nonnegative integers summing to $m-1$, so $S_m=[q^{m-1}](1-q)^{-3}$ and $S_m-S_{m-1}=m$ for $m\ge3$. Equivalently, $S_m=[T^{m+1}]_{0,2}$: a path from $0$ to $2$ in $m+1$ steps advances twice, and we choose those steps.

These states count the sum; they do not represent canonical summands or blue strands.

$\displaystyle
\text{[D169]}$ [D169](../diagram-index.md#d169)


