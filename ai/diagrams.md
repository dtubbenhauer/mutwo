# Reading the diagrams as mathematics

This companion describes the mathematical content of the principal diagrams in *Annular webs and Guralnick's conjecture*. The [complete source](source.tex) and [PDF](source.pdf) retain their exact drawings. The descriptions below supplement those files. In particular, an abstract graph does not determine an annular web: boundary order, orientation, edge thickness, winding, crossing data and normalization also matter.

## 1. Conventions

See [drawing conventions](paper.md#subsec-drawing-conventions), [PDF pages 8–9](source.pdf#page=8), and [source](source.tex#L3605).

Read planar and cut-open diagrams **bottom to top**, and annular diagrams **from the inner boundary outwards**. In $g\circ f$, $f$ acts first; place $g$ above or outside $f$. Horizontal juxtaposition is the planar tensor product. Red dashed lines mark boundaries and cuts; gray lines mark glued boundaries. Identifying the two vertical sides of a strip at equal heights gives the annulus. Matching seam labels mark continuations of the same edge. The cut specifies the start of an ordered boundary.

A thin blue strand has thickness 1, often unprinted. Thickness $a$ denotes a quantum symmetric power; printed line width is schematic. The calculus does not fix an ambient representation rank. Thickness is conserved at every split or merge, and zero-labeled edges are deleted. A crossing has no vertex. A solid trivalent joint and a signed winding dot have different meanings. Bent or horizontal segments abbreviate upward webs; the web category used here has no cups, caps or closed components.

A splitter inside coefficient brackets means extraction in the **normalized standard basis**. It is not composition or closure. Likewise, the scalar evaluation of an ordinary split–merge web is the scalar multiplying its straight strand, not a trace.

## 2. Local generators and relations

See [symmetric webs](paper.md#def-symmetric-webs), [digon and Schur relations](paper.md#eq-web-digon), and [PDF pages 9–10](source.pdf#page=9).

The split $\iota_{a+b,(a,b)}$ has input $(a+b)$ and output $(a,b)$; the merge $\mu_{(a,b),a+b}$ reverses these boundaries. Their split-then-merge composite is

$$
\mu_{(a,b),a+b}\circ\iota_{a+b,(a,b)}
=\begin{bmatrix}a+b\\a\end{bmatrix}\operatorname{id}_{(a+b)}.
$$

The bracket is the symmetric quantum binomial coefficient from the manuscript. Associativity and coassociativity identify the two parenthesizations of three merges or splits. Two nested digons evaluate to $[a+b+c]!/([a]![b]![c]!)$ times the identity.

The Schur relation has input $(a,b)$ and output $(c,d)$, with $a+b=c+d$. Its left side merges and then splits. A summand on the right splits $a$ into $(a-i,i)$ and $b$ into $(j,b-j)$, crosses the middle packets using $H_{i,j}$, and merges to $(c,d)$. Its coefficient is $v^{(a-i)(b-j)}$, summed over $0\le i\le a$, $0\le j\le b$, $i-j=a-c$. Keeping the crossing and this scalar is essential.

On thin strands, the merge–split channel is $b_i=H_i+v\operatorname{id}$. The pictured relations include $b_i^2=(v+v^{-1})b_i$, cancellation of inverse crossings, and the braid relation. Already on three strands,

$$b_1b_2b_1-b_1=C_{s_1s_2s_1}=C_{S_3}.$$

The final diagram is total merge followed by total split. Thus a bar invariant composite need not itself be canonical.

## 3. Winding, rotation and the bar

See [coils](paper.md#fig-cut-guide), [rotation](paper.md#eq-web-rotation), [the bar convention](paper.md#def-hecke-kl-basis), and [PDF pages 10–13](source.pdf#page=10).

A positive thin winding at position $i$ is $X_i$; the negative winding is $X_i^{-1}$. Their composites cancel. The relations read

$$X_iX_k=X_kX_i,\qquad H_iX_iH_i=X_{i+1},\qquad H_iX_k=X_kH_i\quad(k\ne i,i+1).$$

For $1\le a<N$, let $\beta_a$ be the positive crossing lift of $[a+1,\ldots,N,1,\ldots,a]$. Then positive boundary rotation satisfies

$$\rho_N^a=(X_1\cdots X_a)\beta_a,\qquad X_1=\rho_NH_{N-1}^{-1}\cdots H_1^{-1}.$$

For three strands, $\rho_3=X_1H_1H_2$. A determinant dot on a thick edge denotes the product of its thin winding variables. At thickness two, the dotted digon gives $[2]$ times the thick determinant dot. A vertex crossing the cut is an ordinary vertex transported by rotation.

The bar fixes splits, merges and $\rho_N$, and sends $H_{a,b}$ to $H_{b,a}^{-1}$. **It does not merely reverse a winding dot's sign:**

$$\overline{X_1}=\rho_NH_{N-1}\cdots H_1.$$

At $N=3$, the pictured word is $X_1H_1H_2^2H_1$. The source macros `thinword` and `AffineWord` list operations in bottom-to-top execution order; converting them into a multiplication word reverses that list.

## 4. Standard basis and the distinguished splitter

See [the basis dictionary](paper.md#lem-affine-schur-dictionary), [the splitter](paper.md#fig-spherical-boundary), and [PDF pages 14–15](source.pdf#page=14).

The standard-basis sandwich means

$$h_{I_A}[A]_v=\mu_{\omega_N,\alpha}\circ\jmath_N(H_{d(A)})\circ\iota_{\gamma,\omega_N},\qquad
I_A=W_\alpha\cap d(A)W_\gamma d(A)^{-1}.$$

The factor $h_{I_A}$ accounts for repeated symmetrization and must be retained.

The ordinary splitter $B_m$ first splits $N=2m+1$ into $(m,m+1)$ and then splits $m+1$ into $(1,m)$. Its output is $(m,1,m)$, and $[B_m]_v=\theta_{B_m}$. Its longest double-coset representative is $w_0$. The coefficient used in the proof is

$$[[B_m]_v]\theta_{A_{j;m}}=v^{D_{j;m}}P_{w_0,C_{j;m}}(v^{-2}).$$

Its coefficient of $v$ is $\mu_{j;m}$.

## 5. The six maps defining the main web

See [Section 3A](paper.md#s-mainweb), [the symmetrizer expression](paper.md#lem-main-symmetrizer), [PDF pages 15–17](source.pdf#page=15), and [source](source.tex#L4412).

Set $\Lambda=(N)$, $V=(m,1,m)$, $J=(2m,1)$, $L=(1,m-1,1,m-1,1)$ and $K=(1,N-2,1)$. The composite is

$$\Lambda\xrightarrow{a}V\xrightarrow{b}J\xrightarrow{c}L\xrightarrow{d}K\xrightarrow{e}L\xrightarrow{f}V.$$

| Stage | Operation |
| --- | --- |
| a | Ordinarily split $N$ into $(m,1,m)$. |
| b | Merge the two outer $m$-packets across the cut, retaining the middle unit. |
| c | Annularly split to $(1,m-1,1,m-1,1)$, exposing the two outer unit strands. |
| d | Merge the middle three packets $(m-1,1,m-1)$ to $2m-1$. |
| e | Split that middle packet back to $(m-1,1,m-1)$. |
| f | Rejoin each retained outer unit with its adjacent $(m-1)$-packet. |

The two outer units bypass stages d–e. The underlying graph is unchanged as $m$ varies; only thicknesses change.

The boundary names also denote the specific parabolics

$$
\begin{aligned}
W_0&=\langle s_1,\ldots,s_{N-1}\rangle,\\
J&=\langle s_i:i\in\mathbb Z/N\mathbb Z\setminus\{m,m+1\}\rangle,\\
K&=\langle s_2,\ldots,s_{N-2}\rangle,\qquad V=W_0\cap J,\qquad L=J\cap K=K\cap V.
\end{aligned}
$$

Thus the exact parabolic chain is $W_0\supset V\subset J\supset L\subset K\supset L\subset V$. Although $J$ contains $s_0$, it is finite. These data fix which merge crosses the cut, something the boundary sequences alone would not specify.

In the inverse-permutation convention,

$$\mathcal R_m=\frac{M_eC_JC_KC_V}{[m]!^2[m-1]!^4}.$$

This quotient represents the six integral maps. Before applying inversion, their evaluation is $C_VC_KC_JC_{W_0}/(h_Vh_L^2)$; inversion reverses the order.

## 6. The flag diagrams

See [the gallery count](paper.md#lem-finite-flag-count), [standard coefficients](paper.md#prop-gallery-standard), and [PDF pages 17–18](source.pdf#page=17).

The finite quotient diagram is the inclusion chain

$$I_0+L\subset I\subset K\subset K_0\cap H,$$

with dimensions $r+\epsilon,m,m+1,N-r-\eta$. Choosing the middle flag gives

$$\begin{bmatrix}N-2r-\epsilon-\eta\\m-r-\epsilon\end{bmatrix}_Q[m+1-r-\eta]_Q.$$

The lattice diagram additionally records

$$\Lambda'\subset\widetilde L\subset\widetilde I\subset\widetilde K\subset\widetilde H\subset t^{-1}\Lambda',$$

$$\Lambda\subset\widetilde I,\qquad \widetilde K\subset t^{-1}\Lambda,\qquad
\widetilde L\subset\widetilde F\subset\widetilde F'\subset\widetilde H.$$

These additional inclusions matter. The nested-digon pictures express two orders for choosing a $k$-space inside a $(k+1)$-space; they are scalar identities for open webs.

## 7. Auxiliary families and the correction

See [the six families](paper.md#def-six-families), [spherical webs](paper.md#def-spherical-web), [one-line webs](paper.md#def-one-line-web), and [PDF pages 20–25](source.pdf#page=20).

| Family | Construction shown |
| --- | --- |
| A | Full-spherical $\mathcal V_r$, with refined output. |
| B, C | The dual one-line webs $\mathcal E_{r,m+1}^{\vee}$ and $\mathcal E_{r,m}^{\vee}$. |
| D, E | The one-line webs $\mathcal E_{r,m+1}$ and $\mathcal E_{r,m}$. |
| F | The desired canonical indices $A_{r;m}$ occurring in $\mathcal R_m$. |

The family letters are unrelated to Dynkin types. The operation $\vee$ reflects left–right, exchanges the outer edges and reverses winding.

The spherical web $\mathcal V_s$ splits $N$ into $(s,N-s)$, merges and splits across the cut, and ordinarily merges back to $N$. Its canonical differences are $C_{Z_0}=\mathcal V_0$ and $C_{Z_s}=\mathcal V_s-\mathcal V_{s-1}$. Append the ordinary splitter for output $(m,1,m)$.

The one-line web $\mathcal E_{j,f}$ retains one unit and ends at $(f,N-f)$. Its exact symmetrizer formula is in its definition. For strong refinement, split the right $(m+1)$-packet of $(m,m+1)$ into $(1,m)$; for weak refinement, split the left $(m+1)$-packet of $(m+1,m)$ into $(m,1)$. Both end at $(m,1,m)$.

After including multiplicities, the four one-line families contribute only in degree at least 3 at $B_m$. The spherical family does affect degree 1 and is subtracted in $\mathcal R_m^{\mathrm{crit}}$. This corrected web is a sum of desired canonical elements plus auxiliary terms, not generally one canonical element.

## 8. The first example and the counting automaton

See [the complete example](paper.md#sec-aggregate-calibration) and [PDF pages 29–30](source.pdf#page=29).

At $m=2$, the pictured five-term expansion is

$$\mathcal R_2=\theta_{A_{2;2}}+\theta_{A_{1;2}}+\mathcal E_{1,2}+\mathcal E_{1,2}^{\vee}+(v+v^{-1})\theta_{B_2}.$$

The smaller family term is $\theta_{A_{1;2}}=\mathcal U_2-(v+v^{-1})B_2$, where $\mathcal U_2$ corresponds to $M_eb_0b_4b_1$. Hence

$$\theta_{A_{2;2}}=\mathcal R_2-\mathcal U_2-\mathcal E_{1,2}-\mathcal E_{1,2}^{\vee}.$$

Their respective degree-one coordinates are $4,2,0,0$, giving $\mu_{2;2}=2$. For the row sum, removing the source correction instead gives $4-1=3$.

The three-state diagram after the main theorem has weight-one loops at 0,1,2 and edges $0\to1\to2$. Its matrix is $T=\left(\begin{smallmatrix}1&1&0\\0&1&1\\0&0&1\end{smallmatrix}\right)$, with $[T^{m+1}]_{0,2}=\binom{m+1}{2}$. These states count the final sum; they do not represent canonical summands or strands.

<a id="finite-affine-comparison"></a>

## 9. The comparison with the finite paper

The comparison diagram in Remark 1E.1, represented by D018 in the reading edition, contains substantive text. Here is its content as a table. The finite column concerns the earlier paper cited as `Finite`; the affine column concerns this paper. In the first finite entry, fixed rank refers to the planar web calculus; the symmetric groups in the earlier result grow.

| Finite: earlier paper | Affine: this paper |
| --- | --- |
| Repeat planar web blocks; the rank is fixed. | Fix the annular web graph; vary the rank and thicknesses. |
| Standard coefficients via FKK: evaluate explicit local maps on basis words. | Standard coefficients via Hecke–Schur: count intermediate flags to obtain Gaussian polynomials. |
| Correct the blocks on a fixed 28-dimensional connecting space; prove dual canonicality by local bounds. | Use degree bounds, bar symmetry and positivity to restrict canonical terms to six families. |
| Select the required tensor coordinate; reduce the calculation to two states. | The desired terms occur once. Subtract one auxiliary family; four others do not affect degree one. |
| Two more blocks double the coefficient: $\mu(x_{2r},y_{2r})=2^r$. | Gaussian cancellation gives $\sum_{j=1}^m\mu_{j;m}=\binom{m+1}{2}$. |

Source: [the comparison macro](source.tex#L2636-L2697), used in [Remark 1E.1](paper.md#ai-statement-006), [PDF page 7](source.pdf#page=7). The clarification about the two meanings of rank is editorial; the table transcribes the diagram.

## 10. The toroidal closure and Heawood comparison

See [Figure 1](paper.md#fig-toroidal-closure) ([PDF page 2](source.pdf#page=2)), [Figure 6](paper.md#fig-heawood), [Figure 7](paper.md#fig-heawood-moves), and [PDF pages 33–34](source.pdf#page=33).

The main graph's toroidal closure has 14 vertices, 21 edges and faces of lengths $4,4,5,5,6,6,12$. The Heawood embedding has the same vertex and edge counts but seven hexagonal faces. The graphs are not isomorphic. The closure's length-12 face has a repeated boundary walk, not a simple 12-cycle.

The source's Whitehead-move picture displays dual flips $gg\to be$, $bg\to ae$, $fg\to de$, $eg\to af$, $eg\to bf$, $ef\to bc$, read row by row. This comparison concerns embedded graphs. It is not asserted to be an equality of labeled web morphisms.

The [graph data](toroidal-closure.json) record the closure's source-derived edges and oriented face walks. They omit thickness and the open annular boundary, so they cannot replace the six-map definition of $\mathcal R_m$.

## 11. What is checked formally

The [verification remark](paper.md#rem-verification), [PDF pages 7–8](source.pdf#page=7), reports that the Lean development encodes the chosen labeled graph and proves that its specified presentation evaluates to the six-map morphism. It also reports verification of the family, gallery calculations, canonical correction, row sum and cohomological deduction, relative to explicit hypotheses from the literature.

Those hypotheses include the Coxeter and Hecke framework, KL theory and positivity, Schur canonical bases and refinement, flag-orbit classification and convolution, and the representation-theoretic inputs to the cohomological application. They are not themselves formalized in the development described by the paper. Neither the diagrams nor this companion establish that background independently. The graph data supplied here are a transcription checked for incidence consistency; this is separate from checking the repository's Lean build.
