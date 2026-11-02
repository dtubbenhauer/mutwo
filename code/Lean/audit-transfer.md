# Audit of the KL-to-first-cohomology application

Scope: `PolishedWebProof/main.tex`, Sections 1, 2 and 10, read on 2026-10-29. This is a source and convention audit conditional on the manuscript's row-sum theorem. It is not a certification of the web calculation or a Lean proof of the external representation theory. No existing manuscript files were changed.

## Result

I found no mathematical defect in the stated transfer chain. In particular, the original Bendel–Nakano–Pillen theorem supports the prime-field case directly. There is no need to replace `PSL_N(F_p)` by groups over unspecified field extensions. The distinction between a fixed trivial source and two varying irreducible modules is preserved.

The largest remaining verification limitation here is bibliographic: I checked Andersen's cohomological formula in Lübeck's explicit published formulation, rather than directly reading the inaccessible Andersen 1986 full text. Likewise, the sufficiently-large-characteristic assertion is checked in Lübeck's formulation of AJS; the original AJS monograph record was located but its full PDF exceeded the browser's size limit. These are limits of this audit, not identified missing hypotheses in the manuscript.

## 1. Quantifiers and the target conjecture

The conjecture used is an absolute bound for `dim_k H^1(H,M)` over all finite groups H, fields k and finite-dimensional faithful absolutely irreducible kH-modules M. Its formulation agrees with Lübeck, Conjecture 4.4. The original reference is R. M. Guralnick, *The dimension of the first cohomology group*, LNM 1178 (1986), 94–97, [DOI](https://doi.org/10.1007/BFb0075290); I did not retrieve that chapter's full text in this audit.

The manuscript's conclusion has the sufficient quantifier order

`for each m >= 2, for every sufficiently large prime p (threshold depending on m), there exists j in {1,...,m} with dim H^1 >= ceil((m+1)/2)`.

Both rank and characteristic may vary. No fixed-characteristic unboundedness is claimed. An algebraically closed coefficient field is allowed by the conjecture; disproving the restricted algebraically closed formulation already disproves the unrestricted assertion. The row sum establishes existence of a large member of the explicit family, without identifying which member achieves the bound. It does not establish the individual formula `mu_{j;m}=j`.

## 2. Ordinary KL, spherical normalization, and the trivial source

The manuscript uses `(H_i-v^{-1})(H_i+v)=0` and `C_{s_i}=H_i+v`. Its inducing vector has `H_i` eigenvalue `v^{-1}` for finite simple reflections. Thus it is induced trivial, not induced sign. Lübeck Section 2.2 has the same action: at a wall of the finite parabolic, `M_x C_s=(v+v^{-1})M_x`, and canonical lower coefficients lie in `v Z[v]`.

For `u=u_{j;m}` increasing and `b=u^{-1}`, the manuscript's normalized spherical coefficient is

`m_{e,b}(v)=v^D P_{w0,w0*b}(v^{-2})=v^D P_{w0,u*w0}(v^{-2})`.

The second equality is simultaneous inversion: `(u*w0)^{-1}=w0*b`. Since `D` is odd, the coefficient of `v` is exactly the coefficient of `Q^((D-1)/2)` in the ordinary KL polynomial. There is no extra power, no coefficient at `v^{-1}`, and no replacement of `w0` by the identity in the ordinary Hecke algebra. The spherical vector indexed by `e` embeds as `C_{w0}` and represents the trivial highest weight 0.

The source of the Ext group is therefore the Weyl module `V(0)=k`. It is not `L(lambda')` for another varying weight. The window's degree is zero, so the relevant affine element lies in the ordinary root-lattice affine Weyl group, even though the surrounding web category also uses its extension.

## 3. Highest-weight check

Writing `u(i)=z_i+N*s_i`, inversion gives permutation part `z^{-1}` and translation coordinates `-s_i`. Consequently

`(b dot_p 0)_i = -p*s_i + rho_(z_i)-rho_i = -p*s_i+i-z_i`.

For `c=m-j`, this is the sum-zero vector

`(p repeated j-1, p-c-2, 1 repeated c, 0, -1 repeated c, c+2-p, -p repeated j-1)`.

Adjacent differences give precisely `(c+2) eta_(j-1)+(p-c-3) eta_j+eta_m`. At `j=m`, the last two terms overlap, producing `2 eta_(m-1)+(p-2) eta_m`; at `j=1`, `eta_0=0`. The boundary cases are therefore included.

For `p>N`, all Dynkin coefficients are in `[0,p-1]`; the weight is nonzero and dominant. Integral sum-zero coordinates put it in the root lattice. The vector `lambda+rho` is congruent to a permutation of `rho` modulo p, whose distinct coordinate differences have absolute value at most `N-1<p`; hence it is p-regular. This verifies membership in the restricted principal block required by the external results.

## 4. Rational cohomology and characteristic assumptions

[Lübeck's paper](https://arxiv.org/html/1610.07055), Theorem 4.5, states the Weyl-to-simple Ext interpretation assuming its Theorem 3.1 holds and `x dot 0` is dominant and p-restricted. Its explicit `y=1` consequence is `dim H^1(G,L(x dot 0))=[v]m_(1,x)(v)`. Here take `x=b` and `y=1`; the preceding checks supply the hypotheses. The unrelated constant-term issue in its displayed all-degrees formula when `x=y` has no effect here: our target weight is nonzero and only degree one is used.

For each fixed root system, Lübeck Theorem 3.1 asserts the character formula for all but finitely many primes, attributing this to AJS and the effective bound to Fiebig. Thus a rank-dependent sufficiently-large-prime threshold is justified; the numerical comparison bound `p>=5(N-1)` alone is not asserted to imply the character formula.

Original references: H. H. Andersen, *An inversion formula for the Kazhdan–Lusztig polynomials for affine Weyl groups*, Adv. Math. 60 (1986), 125–153, [DOI](https://doi.org/10.1016/S0001-8708(86)80008-1); Andersen–Jantzen–Soergel, *Representations of quantum groups at a p-th root of unity and of semisimple groups in characteristic p: independence of p*, Astérisque 220 (1994), [Numdam record](https://www.numdam.org/item/AST_1994__220__1_0/).

## 5. Original BNP theorem: exact specialization

I read the original journal theorem on page 141, Section 7.5, in the existing local PDF and checked its inequality signs in `RevisedWeb/investigation/root/bnp-transfer-page141.png`. The source is Bendel–Nakano–Pillen, *On comparing the cohomology of algebraic groups, finite Chevalley groups and Frobenius kernels*, J. Pure Appl. Algebra 163 (2001), 119–146, [publisher record](https://doi.org/10.1016/S0022-4049(01)00024-X).

Its hypotheses are `u in Wtilde_p` (the finite Weyl group extended by translations by `p X(T)`), `s>=1`, `p>=(4s+1)(h-1)`, `nu in X_r(T)`, `<nu,alpha_0^vee><2s(h-1)`, and `u dot nu` p^r-restricted. For `0<=i<=s`, its conclusion is

`H^i(G(F_q),L(u dot nu)) ≅ H^i(G,L(u dot 0+p^r nu))`, with `q=p^r`.

Set `s=1`, `r=1`, `nu=0`, `u=b`, `i=1`, and `h=N`. Under the positive p-dot realization, `b` lies in the root-lattice affine subgroup of `Wtilde_p`. All hypotheses hold under the manuscript's assumptions, and both coefficient modules have highest weight `b dot_p 0`. The result is exactly the claimed equality for `SL_N(F_p)`. No Frobenius twist, enlarged field exponent or extra summand survives. The same specialization is stated in Lübeck Theorem 4.6.

## 6. Irreducibility, central descent, and faithfulness

I read [Steinberg's original paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/02AE5498AF62BCAB6B313C75016E6015/S0027763000011016a.pdf/representations_of_algebraic_groups.pdf), *Representations of algebraic groups*, Nagoya Math. J. 22 (1963), 33–56. Sections 6.1 and 7.4 identify restricted rational representations with distinct irreducible finite-group representations. Section 7.6 explicitly describes descent to the central quotient, including the type-A weight congruence.

Thus the nonzero restricted weight gives a nontrivial irreducible `SL_N(F_p)`-module over the algebraically closed field k. It is absolutely irreducible. Its root-lattice highest weight gives trivial action of the algebraic center and hence of the finite center. One can also check the central character directly: each `eta_i=omega_i+omega_(N-i)` has total index N, so its class modulo the root lattice is zero.

For `Z=Z(SL_N(F_p))`, `|Z|=gcd(N,p-1)` is invertible in k. Since Z acts trivially, `H^1(Z,M)=Hom(Z,M)=0`; inflation–restriction gives `H^1(PSL_N(F_p),M) ≅ H^1(SL_N(F_p),M)`. This is an isomorphism, not merely an injection. Finally, `N>=5` avoids the exceptional nonsimple projective groups. A nontrivial irreducible representation of this simple quotient has trivial kernel, hence is faithful.

## 7. Formalization boundary

The installed project pins Lean `v4.22.0-rc2` and mathlib commit `49af9b7fd7e19db08a946b5bd08d1a5bc39dfd3d`. Mathlib has actual `Rep k G`, `groupCohomology A 1`, and `groupCohomologyIsoExt A 1`, whose first Ext argument is `Rep.trivial k G k`. It also defines projective special linear groups and algebraic closures.

A local source search did not locate the Andersen/AJS/BNP transfer theorems, affine KL bases or Steinberg's restricted-module classification. Therefore a Lean proof of an arithmetic implication, even one using actual `groupCohomology`, must leave the row-sum and module-transfer assertions as explicit hypotheses until these external dependencies are formalized. Such a theorem is useful and honest, but is not an unconditional formal proof of Guralnick's conjecture being false.

`Guralnick/Cohomology.lean` now compiles with that explicit boundary. It proves the existence of actual PSL representations with arbitrarily large first-cohomology dimensions from the visible hypotheses `DoubledRowSum` and `PrimeFieldTransfer`. The latter includes finite dimensionality of the actual H1 vector spaces. A `#print axioms` check on the conditional conclusion and on the Ext-from-trivial isomorphism reports only `propext`, `Classical.choice`, and `Quot.sound`, with no additional axioms or `sorryAx`.

## Suggested precision improvements, not mathematical repairs

- Cite Steinberg Section 7.6 alongside 7.4 for the center quotient.
- State the BNP substitution in a displayed line if maximal auditability is desired; the current prose substitution is correct.
- Keep the ordinary KL source `w0`, the spherical source `e`, and the rational Ext source `k` visibly distinguished.
- Describe Lean output as a conditional formal implication unless the external representation theory and web row sum have actually been supplied as kernel-checked proofs.
