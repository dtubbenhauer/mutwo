# 6. Application to Guralnick's conjecture

Part of *Annular webs and Guralnick's conjecture*, snapshot 2026-11-03. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.

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


**Lemma 6A.2.** [Source](../source.tex#L5811); [PDF p. 31](../source.pdf#page=31).


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

Write $u=u_{j;m}$ and $b=u^{-1}$. The increasing window is $u(i)=z_i+Ns_i$, with $1\le z_i\le N$; thus $b$ has permutation part $z^{-1}$ and translation coordinates $-s_i$. Hence $(b\cdot_p0)_i=-ps_i+\rho_{z_i}-\rho_i=-ps_i+i-z_i$. The negative-shift residues are $(1,\ldots,j-1,m+2)$, the positive-shift residues are $(m,N-j+2,\ldots,N)$, both in increasing order, and the remaining shifts are zero. Substitution gives [Equation 6A.3](../paper.md#eq-application-coordinates); adjacent differences give [Equation 6A.1](../paper.md#eq-application-weight).

For $j<m$, the nonzero fundamental-weight coefficients $c+2$, $p-c-3$, $1$ lie in $[0,p-1]$; for $j=m$, the weight is $2\eta_{m-1}+(p-2)\eta_m$, again dominant and restricted. The nonzero integral sum-zero vector lies in the root lattice. Finally, $\lambda+\rho$ is congruent modulo $p$ to a permutation of $\rho$, whose coordinate differences have absolute value between $1$ and $N-1<p$. Thus $\lambda$ is $p$-regular.

*End of proof.*


<a id="section-6b"></a>

### 6B. The cohomology coefficient

<!-- Source: source.tex lines 5842; PDF page 31. -->


Henceforth assume $p\ge5(N-1)$ and Lusztig's character formula for the $p$-restricted weights of $G$. For fixed $N$, all sufficiently large primes satisfy both conditions [[AJS94](../paper.md#bib-ajs)]; see [[Lüb20](../paper.md#bib-luebeck), Theorem~3.1].


<a id="prop-application-transfer"></a>


**Lemma 6B.1.** [Source](../source.tex#L5849); [PDF p. 31](../source.pdf#page=31).


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

Since $u=u_{j;m}$ is right finite-minimal, $b=u^{-1}$ is left finite-minimal. By [Section 2](../paper.md#sec-dictionary), its normalized spherical coefficient at $M_e$ is 

```latex
m_{e,b}(v)=v^{D_{j;m}}P_{w_0,w_0b}(v^{-2})
=v^{D_{j;m}}P_{w_0,C_{j;m}}(v^{-2})
=\big[[B_m]_v\big]\theta_{A_{j;m}}.
```

 Here $w_0b=C_{j;m}^{-1}$, and KL polynomials are invariant under simultaneous inversion. Thus $[v]m_{e,b}(v)=\mu_{j;m}$. Andersen's cohomological interpretation [[And86](../paper.md#bib-andersen)], as in [[Lüb20](../paper.md#bib-luebeck), Theorem~4.5], gives 

```latex
[v]m_{e,b}=\dim_k\operatorname{Ext}^1_{G}\big(k,L(b\cdot_p0)\big)
=\dim_k H^1\big(G,L(b\cdot_p0)\big).
```

 The dominant restricted hypothesis is [Lemma 6A.2](../paper.md#lem-application-weight).

The Coxeter number is $N$, so Bendel--Nakano--Pillen comparison [[BNP01](../paper.md#bib-bnp), Theorem~7.5], in the form [[Lüb20](../paper.md#bib-luebeck), Theorem~4.6], applies for $p\ge5(N-1)$, cohomological bound $s=1$, base weight $\nu=0$ and field exponent $r=1$, giving the finite group equality. Steinberg's restricted-module theorem [[Ste63](../paper.md#bib-steinberg), Theorems~1.3, 6.1 and 7.4] gives irreducibility on restriction; see also [[Lüb20](../paper.md#bib-luebeck), Proposition~5.3]. The nonzero restricted weight gives nontriviality, and algebraic closure of $k$ gives absolute irreducibility.

*End of proof.*


<a id="section-6c"></a>

### 6C. Passage to the finite simple quotient

<!-- Source: source.tex lines 5890; PDF page 32. -->


We now wrap up.


<a id="lem-simple-quotient"></a>


**Lemma 6C.1.** [Source](../source.tex#L5894); [PDF p. 32](../source.pdf#page=32).


The restricted module $L(\lambda_{j;m}(p))$ descends to a faithful absolutely irreducible module $M_{j;m}(p)$ for $H=\mathrm{PSL}_N(\mathbb F_p)$, and 

```latex
H^1\big(H,M_{j;m}(p)\big)
\cong H^1\Big(\mathrm{SL}_N(\mathbb F_p),L\big(\lambda_{j;m}(p)\big)\Big).
```


**Proof.**

The root-lattice condition makes the algebraic center act trivially. The finite center has order $\gcd(N,p-1)$, prime to $p$, so averaging and inflation--restriction give the isomorphism. Descent preserves absolute irreducibility and nontriviality. Since $N\ge5$, the group $H$ is nonabelian simple; its nontrivial representation is therefore faithful.

*End of proof.*


<a id="cor-guralnick"></a>


**Corollary 6C.2.** [Source](../source.tex#L5913); [PDF p. 32](../source.pdf#page=32).


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

Transfer identifies the summands with $\mu_{j;m}$. Apply [Theorem 4L.1](../paper.md#thm-aggregate-web), average and use integrality; the lower bound tends to infinity.

*End of proof.*

For $m=2$, the Dynkin coordinates are $(p-4,1,1,p-4)$ and $(2,p-2,p-2,2)$. Under the stated characteristic assumptions, the first cohomology dimension for $H=\mathrm{PSL}_5(\mathbb F_p)$ is read from the normalized standard expansion of the corrected web: 

```latex
\begin{gather*}
\dim_k H^1\big(H,M_{1;2}(p)\big)
=[v]\,\left[\,\text{[D186]}\,\right]\!\left(\text{[D187]}-(v+v^{-1})\text{[D188]}\right)
=[v](v+v^3)=1.
\end{gather*}
```

 [D186](../diagram-index.md#d186); [D187](../diagram-index.md#d187); [D188](../diagram-index.md#d188)

 For $M_{2;2}(p)$, the four pictured terms in [Section 5](../paper.md#sec-aggregate-calibration) give $4-2-0-0=2$. The passage from these web coordinates to cohomology uses [Lemma 6B.1](../paper.md#prop-application-transfer) and [Lemma 6C.1](../paper.md#lem-simple-quotient).

For fixed root systems, first cohomology in defining characteristic is bounded by Cline--Parshall--Scott [[CPS09](../paper.md#bib-cps)], and first extensions by Parshall--Scott [[PS11](../paper.md#bib-parshallscott)]. For cross characteristic see [[GT11](../paper.md#bib-guralnicktiep), [GT20](../paper.md#bib-guralnicktiepsectional)]; for quantitative bounds in growing rank see [[PS14](../paper.md#bib-parkerstewart)]. The ranks in our construction grow. By contrast, the earlier value $469>63=\dim\mathrm{SL}_8$, independently checked by Scott and Sprowl shortly after the June 2012 AIM workshop, already sufficed for the Wall counterexamples discussed in the introduction [[G+12](../paper.md#bib-aimwall), [Lüb20](../paper.md#bib-luebeck)]. Varying the field alone need not increase first cohomology.


