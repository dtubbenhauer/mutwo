# Andersen source follow-up

30 October 2026. This supplements [audit-primary-transfer.md](audit-primary-transfer.md)
and changes no mathematical interface, Lean declaration or manuscript text.

**The original 1986 Ext theorem remains unread.** Two accessible papers by
Andersen now identify the relevant original propositions, but neither supplies
a substitute theorem in precisely the modular category and conventions used
here. The exact degree-one statement is still supported by Lübeck's account.
No definite mathematical mismatch was found in this follow-up; this is a
remaining source-verification limitation, not evidence that the transfer is
false.

## What the additional original-author sources establish

In [Andersen, *Extensions of simple modules for quantum groups at complex
roots of 1*, arXiv:2508.12898v1](https://arxiv.org/html/2508.12898v1), §5,
printed p.14, Andersen identifies §2 of his 1986 paper as the earlier modular
KL–Ext result, conditional on the modular character formula. The proof of
Theorem 5.2, printed p.15, points specifically to **Propositions 2.8 and 2.12**
of that paper: the former compares extensions with simple and induced
modules; the latter supplies the KL coefficient formula.

The displayed Theorem 5.2 concerns the **quantum** category. Its labels start
in an antidominant alcove and involve additional wall/reflection conditions.
It is therefore not a direct verification of the present rational algebraic
group statement with the fixed trivial source. Its usefulness here is to
locate the original result, not to supply an additional transfer hypothesis.
The [page image](literature-audit/andersen/Andersen2025-p15.png) was checked.

The university preprint of [Andersen–Stroppel, *Twisting functors on
O*](https://data.math.au.dk/publications/pp/2003/imf-pp-2003-1.pdf),
Proposition 7.9 and its proof, printed pp.17–18, independently identifies
Andersen 1986 **Proposition 2.12** as the model for a KL–Ext proof. This is a
statement in finite BGG category O, so it also cannot replace a modular
cohomology theorem. See the [checked proof page](literature-audit/andersen/AndersenStroppel2003-p18.png).

## The convention check that is supported

[Lübeck, arXiv:1610.07055v2](https://arxiv.org/html/1610.07055v2),
§2, uses representatives of `W_J \ W` characterized by **no finite left
descents**, despite calling them right coset representatives. The right
Hecke module has the trivial, spherical parabolic action; its lower canonical
coefficients lie in `v Z[v]`. These agree with the code's
`finiteLeftMinimal` and normalization. They are not antispherical conventions.

Lübeck's Theorem 4.5 requires dominant `x·0`, `y·0`, a p-restricted `x·0`,
and validity of the character formula. Its source is the **Weyl module**
`V(y·0)`, not an arbitrary simple module. Its following paragraph explicitly
sets `y=e`, obtaining `V(0)=k` and first cohomology from the coefficient of
`v`. The [theorem page](literature-audit/andersen/Luebeck2017-p11.png) was
checked. The degree-zero omission in the printed all-degrees sum does not
affect this degree-one use. Lübeck cites Andersen or Jantzen 2003, Appendix
C.2 and C.10.

In the project's notation, the needed comparison is consequently

\[
\dim H^1_{\mathrm{rat}}(SL_N,L(b\mathbin{\cdot_p}0))
=[v]m_{1,b}(v)=[v]h_{w_0,w_0b}(v).
\]

Here the second equality uses the existing **general spherical/ordinary
dictionary**, not an additional claim obtained from the two new papers.
For finite-left-minimal `b`, put `D=ℓ(b)`. The dictionary gives
`m_(1,b)(v)=v^D P_(w0,w0*b)(v^-2)`: no extra length shift remains since
`ℓ(w0*b)=ℓ(w0)+ℓ(b)`. If `D` is odd, its coefficient of `v` is the
coefficient of `Q^((D−1)/2)` in the ordinary polynomial. For `b=e` this
coefficient is zero. In the family, `b=u⁻¹`; simultaneous inversion changes
`(w0,w0*b)` to `(w0,u*w0)`, preserving the fixed lower endpoint. The code
uses this same pair, rather than moving both cohomological sources.

## Precise remaining verification

The next primary text to inspect is Andersen 1986, §2, especially
Propositions 2.8 and 2.12 and their standing assumptions. The required check
is the modular weight region, any regularity or wall conditions, the base
alcove and label conversion, the cohomological direction, and the polynomial
parameter. The eventual characteristic bound must work for **all relevant
restricted labels at a fixed rank**, not merely one chosen label. The
existing AJS audit addresses the character-formula part; these follow-up
sources do not independently certify this entire bundle.

Jantzen 2003, Appendix C.2 and C.10, is a precise alternative exposition to
inspect. The local 1985 Part I preprint does not contain that appendix.
Neither an arbitrary-pair simple Ext formula nor the quantum/category O
analogues close this task.

Publisher metadata for the 1986 article was already available. A further
public PDF request returned HTTP 403; no original PDF was obtained. Access
failure is not a mathematical objection. The new downloads, extraction
commands and hashes are recorded in
[literature-audit/andersen](literature-audit/andersen/README.md).
No external theorem was added to or removed from the formalization. In
particular, this audit does not upgrade the conditional counterexample to
an unconditional machine-checked theorem.
