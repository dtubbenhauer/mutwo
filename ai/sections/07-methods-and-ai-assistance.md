# 7. Methods and AI assistance

Part of *Annular webs and Guralnick's conjecture*, snapshot 2026-11-03. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.

<a id="section-7"></a>

## 7. Methods and AI assistance

<!-- Source: source.tex lines 5958; PDF page 32. -->


We explain how we found the construction and how AI entered the picture. The route was rather less tidy than the proof, so this section is written in an anecdotal style.


<a id="section-7a"></a>

### 7A. Our previous work as a starting point

<!-- Source: source.tex lines 5962; PDF page 32. -->


One prejudice we have acquired over the years is that once things get bad, they tend to get as bad as they possibly can. We have encountered versions of this phenomenon in rather different settings, from the prevalence of torsion in intersection cohomology [[BT26](../paper.md#bib-torsionproliferation)] to the failure of standard link invariants to distinguish large families of links [[K+25](../paper.md#bib-linkdetection)]. Lübeck's computations [[Lüb20](../paper.md#bib-luebeck)], with first cohomology dimensions already running into the millions, certainly encouraged that prejudice here. We found it hard to believe that an absolute bound was waiting somewhere beyond them.

This paper grew out of our earlier work [[G+26b](../paper.md#bib-finite)], where we used planar $\mathfrak{sl}_3$ webs to construct $\mu$-coefficients growing exponentially with $n$ in the symmetric groups $\mathrm{Aut}(\{1,\dots,n\})$. The construction repeats a small piece of web and controls the correction needed to obtain a canonical basis element. A complicated family of permutations thus becomes a fairly simple family of pictures. We wondered whether the same way of thinking could settle Guralnick's conjecture. There was an extra difficulty: large extension dimensions between arbitrary simple modules do not automatically give large first cohomology. For that, one of the modules must be trivial.

So we boldly asked GPT Astra 6.0: "Use our $\mu$-paper to solve Guralnick's conjecture." It first searched the literature and came back with the familiar obstruction: first cohomology requires the lower endpoint to be $w_0$, so an arbitrary family of large $\mu$-coefficients is not enough. It pointed us to [[SX10](../paper.md#bib-sx), Section~4, final remark], where Scott--Xi explicitly leave open whether the coefficients $\mu(w_0,w)$ corresponding to first cohomology can be unbounded. Quite right, but hardly news to us. The silly part was treating this as a reason to stop.

So we took a stick and gave it a poke: "Come on, you do not have to take the request literally. Use the ideas and change the construction if necessary." It then obliged. Unfortunately, we did not understand the answer, and we went back to thinking about what a solution ought to look like.


<a id="section-7b"></a>

### 7B. Put hexagons on an annulus

<!-- Source: source.tex lines 6008; PDF page 33. -->


The guiding idea was simple enough: $\text{affine}=\text{annular}$. Putting diagrams on an annulus to obtain affine versions of familiar algebras is an old theme, going back several decades; see [[HT27](../paper.md#bib-ht), Section~1B] for some historical background. Since the coefficients relevant to first cohomology live in affine KL theory, we should try putting our webs on an annulus.

There was also a more specific picture in mind. The connection between tensor canonical bases and KL polynomials [[FKK98](../paper.md#bib-fkk)] makes the difference between a web and a canonical basis element particularly relevant. KK [[KK99](../paper.md#bib-kk99)] showed that the $\mathfrak{sl}_3$ web basis need not be dual canonical. Their "hexagon-in-hexagons" picture (a central hexagon surrounded by six others, see the right of [Figure 6](../paper.md#fig-heawood)) is a memorable example of where the two bases start to disagree. Related hexagonal patterns supplied the growing webs in [[G+26b](../paper.md#bib-finite)]. Hexagons seemed a good place to look for trouble.

When we tried wrapping these pictures around an annulus, they reminded us of the classical embedding of the Heawood graph on a torus. This graph has $14$ vertices and $21$ edges, and the embedding has seven hexagonal faces. It can itself be drawn as one hexagon surrounded by six others, with suitable boundary identifications; see [Figure 6](../paper.md#fig-heawood).


<a id="fig-heawood"></a>


[D189: drawing](../diagram-index.md#d189) **Figure caption.** The Heawood graph, drawn in the plane and on a torus. On the right, identify opposite three-edge boundary paths with matching letters and arrows. The dashed red curves mark these pairings. The quotient has 14 vertices, 21 edges and seven hexagonal faces.

Cutting the torus open along a suitable noncontractible curve gives an annulus, with the cut edges ending on its boundary. The Heawood graph therefore looked like a rather tempting starting point: a tiny graph built from exactly the sort of hexagons we were looking for. We tried to turn this picture into a family of annular webs and work out the relevant $\mu$-coefficients. It did not quite work, but the picture still looked promising.


<a id="section-7c"></a>

### 7C. A little help with the graph

<!-- Source: source.tex lines 6119; PDF page 33. -->


In the earlier planar calculation, AI assistance had helped us modify an initial web family and find a canonical correction that worked uniformly [[G+26b](../paper.md#bib-finite), Section~9]. That suggested trying the same division of labor here. We gave GPT Astra 6.0 the picture and asked it to make the idea work: massage the graph a little if necessary, and try to find a counterexample to Guralnick's conjecture.

It succeeded fairly quickly. The construction seems to generalize one of Scott--Xi's examples [[SX10](../paper.md#bib-sx)], and looks rather natural when drawn on an annulus. This time we could understand the proof: the picture helped us see what the formulas were doing. The writing, however, was terrible. We took the argument as a blueprint and worked it into the present paper.

The resulting graph is not the Heawood graph, although its toroidal closure still has $14$ vertices and $21$ edges; compare [Figure 1](../paper.md#fig-toroidal-closure). The particularly pleasant surprise is that the graph itself need not grow. In the planar construction we repeated web pieces; here we keep the graph and change only the edge thicknesses. This is enough to produce unbounded first cohomology.

<a id="ai-statement-057"></a>


**Remark 7C.1.** [Source](../source.tex#L6147); [PDF p. 34](../source.pdf#page=34).


The resemblance to the Heawood graph is rather concrete: our toroidal closure is just six Whitehead H=I moves away from its standard torus embedding; see [Figure 7](../paper.md#fig-heawood-moves).


<a id="fig-heawood-moves"></a>


[D190: drawing](../diagram-index.md#d190) **Figure caption.** Six Whitehead moves from our closure to the Heawood embedding. Colors and letters track the seven faces; $pq\to rs$ denotes the edge flip, with the sequence read row by row. Identify opposite dashed sides on the left, and boundary paths with matching letters on the right, following the arrows. The numbers record face lengths.

::: samepage
<a id="ai-statement-058"></a>


**Remark 7C.2.** [Source](../source.tex#L6293); [PDF p. 34](../source.pdf#page=34).


Our construction varies only the edge thicknesses. We suspect that things get considerably worse if the web graph itself is also allowed to grow, but we cannot yet prove a stronger growth statement this way. In the large-characteristic-setting considered here, Lübeck's argument bounds first cohomology dimensions for restricted irreducible modules by $2^{O(r^3)}$, where $r$ is the rank [[Lüb20](../paper.md#bib-luebeck), Remark~(d) after Theorem~4.7]. There is plenty of room between this upper bound and our linear lower bound.
:::

The geometric idea helped us ask a more useful question, and the machine helped turn that idea into a family and a calculation that worked. Responsibility for the mathematics remains ours.


