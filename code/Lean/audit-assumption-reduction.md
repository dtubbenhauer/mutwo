# Three external assumptions replaced by Lean proofs

30 October 2026. All changes are under `code/`; the manuscript and research
files are unchanged. This follows the earlier graph-identification audit.
The final mathematical target remains the same fixed-source row theorem
and its conditional first-cohomology application.

## The parabolic scalar

The scalar is still the manuscript's actual Laurent sum over the actual
finite parabolic subgroup, with exponents `length(longest)-2*length(w)`.
Its definition has not been changed.

`ParabolicWeb.scalar_ne_zero` evaluates this sum at `v=1`. Its value is the
positive cardinality of the subgroup. This uses finite longest-element data,
not a parabolic law or an assumption about the desired coefficients.

`ParabolicWeb.Laws.scalar_bar` starts with the already assumed general
absorption identity at equal parabolics, `C_I*C_I=h_I • C_I`. Applying bar
and using the existing canonical basis produces an equality between the
scalar multiples `h_I • C_I` and `invert(h_I) • C_I`. Taking the coordinate
of `C_I` proves bar invariance. There is no division or localization.

The `scalar_ne_zero` and `scalar_bar` fields have been removed from
`ParabolicWeb.Laws`. Their old method names now denote theorems, so all
clients use proofs of these properties rather than separate premises.
Bar invariance still depends on the existing general absorption and KL
inputs; it is not an independent construction of KL theory.

## The one-period lattice lift

`LaurentLattice.interval_lift` proves the exact former input for every field,
every ambient dimension (including zero), every actual full power-series
lattice Λ, and every vector subspace A between Λ and t⁻¹Λ.

For a power series f, write f as its constant term plus t times another
power series. Since tA lies in Λ, this proves that A is stable under every
power series. Multiplication by t embeds this module into Λ; Noetherianity
of k[[t]] and finite generation of Λ then give finite generation of A.
Its Laurent-series span is full because it contains Λ.

The proof constructs the actual lattice, rather than asserting that a
numerical dimension can be realized. The lower-endpoint theorem recovers
Λ, and the upper-endpoint theorem identifies the constructed module with
the actual image under multiplication by t⁻¹. No quotient-dimension or
lattice-realization input occurs in this construction.

The `interval_lift` field has been removed from `LaurentLattice.Theory`.
Its compatibility method delegates to the new theorem and does not use
its retained theory parameter. The remaining four fields are unchanged.

## Integrity and scope

An independent read-only review found no changed mathematical objects,
restricted parameter ranges, or replacement assumptions. The same graph,
six-map element, canonical correction, ordinary KL row and named modules
remain in the final argument.

The full `python3 scripts/verify.py` run passed: 136 Lean sources built,
133 principal declarations audited, identical regenerated certificates, and
an unchanged manuscript hash. Only `propext`, `Classical.choice` and
`Quot.sound` occur in the principal axiom reports (some use fewer). The
principal proofs are included in `Guralnick/AxiomAudit.lean`. Build and axiom results
are in `reports/verification.json` and `reports/axioms.txt`. The previous
135-source baseline is retained as
`reports/pre-literature-reduction-verification.json`.

These reductions do not settle the entire literature interface. In
particular, the polynomial/completed-lattice comparison, geometric
convolution realization and representation-theoretic transfer remain
explicit external inputs. The primary-source reviews are
`audit-primary-affine.md` and `audit-primary-transfer.md`. An unconditional
Lean counterexample has not been obtained.


Subsequent work constructs the four remaining lattice-theory fields and
removes the whole lattice-theory premise from the external bundle. See
[audit-lattice-completion.md](audit-lattice-completion.md) and
`reports/lattice-assumption-reduction.json`. The counts above record the
earlier 136-source validation; `status.md` gives the current state.
