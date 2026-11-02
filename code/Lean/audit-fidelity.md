# Fidelity audit of the formalization

**Follow-up:** the specific graph-evaluation gap recorded below was subsequently
closed for the manuscript's fixed checked presentation. See
[graph-evaluation.md](graph-evaluation.md) for the new proofs and exact scope.
The remainder of this report records the earlier audit state; current build
and completion status are in [status.md](status.md).

30 October 2026. Target: `../main.tex`, SHA-256
`082e7c5d3f539f389d05c68eeb151ee6e1efd2364475973735ea03cb72b6c361`.
The manuscript and pre-existing research files have not been edited.

## Conclusion and its limits

This audit found no definite replacement of the manuscript's affine
family, prescribed lower endpoint, row-sum statement, correction, or
cohomological target. The final Lean implication follows the paper's
direct six-map integral algebraic argument and concludes unbounded H^1
for actual faithful absolutely irreducible representations of actual
finite simple PSL groups, conditional on the explicit literature inputs.
It does not merely interpret an arbitrary integer sequence as cohomology.

There is a specific coverage gap: **no evaluation theorem connects the
separately defined ribbon graph `Web.family` to the six-map element
`ParabolicWeb.Family.raw`.** The algebraic construction is explicitly in
the paper and is the construction used in the formal proof. The graph's
incidences, thicknesses and boundary masks have substantial checks, but
these cannot certify its winding-sensitive evaluation. Thus “the complete
graphical proof is formalized” would overstate the result.

This is an adversarial audit, not a proof that every assumed framework
interface is jointly realizable or follows from its cited paper. No
unconditional Lean counterexample is claimed. Detailed inputs and source
qualifications remain in [literature-inputs.md](literature-inputs.md).

## The mathematical chain that was checked

| Stage | What is actually represented and proved |
|---|---|
| Family | Actual periodic affine permutations, the prescribed shift sets, sorted `u`, `C=u*w0`, actual intersection matrices and inversion-count lengths. |
| KL coefficient | The coefficient of the ordinary polynomial at exactly `(w0,C)`. The length gap and degree normalization are proved separately. Inversion for the spherical transfer is explicit. |
| Integral word | Actual inclusions and merges on parabolic Hecke right ideals. Its cleared symmetrizer expression is a theorem, not a definition by division. |
| Counting | Actual power-series lattices, quotient flags and gallery equivalences. The four-case formula is derived from generic finite-flag enumeration inputs. |
| Canonical correction | Coordinates, bar symmetry, support, auxiliary canonicality, multiplicity bounds and contribution margins are proved before extracting the critical coefficient. |
| Uniform conclusion | The sum over exactly `1<=j<=m` is `choose(m+1,2)`. The stronger individual formula `mu_(j;m)=j` is neither assumed nor proved. |
| Application | The paper's actual highest weights select algebraic representations; restriction and central descent produce the named PSL representations. The fixed trivial source, characteristic bounds, faithfulness and absolute irreducibility are tracked. |
| H^1 | Mathlib's actual first group cohomology. The Andersen/AJS and BNP comparison theorems are explicit literature parameters, with the actual indices and source conditions. |

The detailed line-by-line reviews are:

- [Original calculation](audit-fidelity-original.md): family, degree and
  matrix conventions, count, six support types, auxiliary bounds,
  correction, row readout and boundary cases.
- [Web and framework](audit-fidelity-web.md): orientation, normalization,
  convolution quantifiers, actual matrix and finite-flag interfaces, graph
  definitions and what their checks do not imply.
- [Cohomological transfer](audit-fidelity-transfer.md): actual modules,
  weight formula, ordinary/spherical indices, trivial source,
  characteristic bounds, center, finite simple quotient and scalar extension.

## New kernel-checked fidelity theorems

These checks add no new literature assumptions and do not change the
mathematical statement of the existing counterexample theorem.

1. **KL rigidity** — [FidelityKL.lean](Guralnick/FidelityKL.lean) proves that
   two realizations of the stated KL interface on a fixed actual Coxeter
   model have the same standard basis, bar, canonical basis and ordinary
   polynomials. Polynomial normalization is injective. Consequently the
   family coefficients cannot be assigned a convenient answer through a
   different choice of basis witness. Existence of the full framework is
   still external; uniqueness alone does not prove consistency.
2. **Exact highest weight** — [FidelityWeights.lean](Guralnick/FidelityWeights.lean)
   proves that both the actual integral vector and its Dynkin labels agree
   with `(c+2) eta_(j-1)+(p-c-3) eta_j+eta_m`. The explicit eta vectors are
   also proved equal to `omega_r+omega_(N-r)` in standard rational
   coordinates. The identities hold uniformly, including `j=1`, `j=m`
   and both displayed `m=2` examples, without any cohomological assumption.
3. **Graph cuts** — [FidelityWeb.lean](Guralnick/FidelityWeb.lean) selects
   edges from actual source/target incidence and proves that all seven
   recorded frontiers have exactly these source ports and thicknesses.
   Its conclusion is list permutation, not ordered equality, accumulated
   winding agreement, annular isotopy or evaluation.

Principal declarations are included in `Guralnick/AxiomAudit.lean`. The
complete verification command is `python3 scripts/verify.py`; current
results are in [status.md](status.md) and `reports/verification.json`.

## Independent experimental checks

Both scripts were rerun successfully during this audit. They enumerate
finite mathematical objects independently of the existing KL engine and
of the formal proof's use of literature inputs:

```sh
python3 scripts/audit_finite_gallery_fidelity.py
python3 scripts/audit_web_interfaces.py
```

- All 20 admissible matrices with row sums `(2,1,2)` and balanced outer
  columns: direct enumeration of actual flags in `F_2^5` agrees with each
  of the four cases and with the encoded polynomial. All 374 subspaces
  of that vector space are enumerated.
- 30,660 window/composition pairs: the periodic dimension, length,
  maximality converse and uniqueness tests pass for all balanced shifts
  in `{-1,0,1}^N`, `3<=N<=7`, and all positive zero-cut compositions.
- 8,214 finite-flag formulas: all actual subspaces in dimensions zero
  through four over `F_2`, including invalid-dimension boundary cases.
- Rank-one empty-chain and roundtrip convolution normalization at
  `Q=p^2`, `v=1/p`, for `p=2,3,5,7`.

These are **experimental checks, not Lean certificates or uniform proofs**.
Do not use Python's `-O` option; the scripts use assertions. JSON results
are in `reports/fidelity-finite-gallery.json` and
`reports/fidelity-web-computations.json`.

## Remaining external and uncovered parts

- All fields of `Hecke.TheoryFamily`, `WebLiterature` and
  `LiteratureTransfer.Inputs` remain explicit external inputs, with their
  bibliographic scope and qualifications listed in the literature ledger.
  This includes the polynomial/completed-lattice comparison and cyclic
  facet interpretation, not just representation theory.
- The graph-to-six-map evaluation just described remains unformalized.
  [gaps.md](gaps.md) explains a concrete way to add it. This is a coverage
  gap, not an established mathematical error in the manuscript.
- The supplied full individual seed KL polynomial has only its Laurent
  normalization verified; its identity as that KL polynomial has no
  verified recursion certificate here. The uniform row proof does not
  depend on that identification.
- No fixed-characteristic unboundedness or individual additive rule is
  concluded.

Stale introductory comments in `Cohomology.lean` and `Counterexample.lean`
were corrected to point to the later final assembly. No mathematical
assumption was strengthened and no main theorem was weakened in this audit.
