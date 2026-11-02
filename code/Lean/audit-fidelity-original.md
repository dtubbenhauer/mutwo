# Independent fidelity audit: original family and web calculation

**Follow-up:** the specific graph-evaluation gap recorded below was subsequently
closed for the manuscript's fixed checked presentation. See
[graph-evaluation.md](graph-evaluation.md) for the new proofs and exact scope.
The remainder of this report records the earlier audit state; current build
and completion status are in [status.md](status.md).

Audit date: 30 October 2026. Scope: the original algebraic/combinatorial
argument of `../main.tex`, primarily Sections 2–8 and the seed calibration.
The generic literature interfaces and representation transfer are being
reviewed separately. This report does **not** certify that those inputs
are consistent or follow from their citations.

No applicable `AGENTS.md` was found. I read the project README, status and
proof map, then checked the source definitions and proofs against the TeX.
Earlier positive audit conclusions were not taken as premises.

## Principal result of this part of the audit

I found no change of family, lower KL endpoint, row-sum target, support
pattern, or correction in the original calculation layer. The code does
not define the KL values to be the claimed answer. Its contribution bounds
are actual theorem applications to the actual canonical expansion.

There is a concrete coverage limit: the formalized ribbon graph is not
connected to the algebraic word by a formal graph-evaluation theorem.
The row theorem proves the manuscript's **direct integral parabolic-map
argument**, with separately checked diagram data. It does not formally
prove a global annular-web interpretation. Details follow below.

## Direct comparisons

| Manuscript | Lean source checked | Finding |
|---|---|---|
| Explicit shifts and sorted window in Section 2 | `Affine.lean:138`–`145`; `Family.lean`, `winding_eq_inputShift`, `window_eq_familyWindow` | The same one-based shift sets, including both isolated residues and empty intervals. The actual affine permutation is proved equal to this independently sorted list. |
| `C=u*w0`, ordinary lower endpoint `w0` | `AffineGroup.lean`, `Family.upper`; `Hecke.lean:143`, `familyMu`; `KLFamily.lean:21` | The critical value is extracted from the actual polynomial at `(w0,C)`. The length gap is proved from inversion counts, not defined to equal the proposed formula. |
| Period-three matrix in columns `-2,1,4` | `Affine.lean:147`–`163`; `FamilyMatrix.lean`, `FamilyUpperMatrix.lean` | Entries are actual translated-window intersection counts. The prescribed matrix is a separately proved target. Columns outside the indicated support are also treated. |
| Six maps, TeX lines 3800–4000 | `ParabolicWeb.lean:150`–`171`; `SphericalMaps.lean`; `CanonicalChains.lean` | The left-acting word is `C_V C_K C_J C_W0/(h_V h_L^2)`, matching the paper before its inverse anti-involution. The formal raw element is a composite of integral maps; division is a proved cleared identity. |
| Four finite-gallery cases, TeX lines 4010–4200 | `GalleryCounting.lean`; `MainGalleryCount.lean`; `CanonicalGallery.lean:122`–`143` | The actual flags have dimensions `(1,m,m+1,N-1)` and the paper's containment constraints. Substituting `b=a+beta`, `c=l+s`, `d=l+s+delta` into the manuscript count gives the four Lean summands exactly. |
| Matrix parametrization and codimension, TeX lines 4280–4340 | `CanonicalMatrix.lean:17`–`119`; `FamilyLength.lean` | Parameters and feasibility are extracted from nonnegative matrix entries and margins. The periodic dimension is evaluated independently of the closed codimension expression. |
| Six support types and degree allowances | `CanonicalGallery.lean`; `CanonicalMultiplicityBounds.lean`; `MainContributionSupport.lean` | The zero-corank case is separate. Type F is identified with the actual family; full type is identified with the actual `Z_r`. No arbitrary numerical states are declared to represent canonical elements. |
| Auxiliary canonicality and margins | `CanonicalOneLineCanonical.lean`; `CanonicalOneLinePatterns.lean`; `MainContributionBounds.lean:90`–`183` | Canonicality is derived from coordinates, leading term, bar and proper degrees. Strong/weak marked margins are `2h+2`/`2h+4`; source and spherical margins are at least three. Reflection acts on actual windows and canonical coordinates. |
| Explicit `g_l`, TeX lines 5072–5082 | `CanonicalCorrection.lean:76`–`83` | `Finset.range(l-1)` is exactly `0,...,l-2`; `g_1=0`. No erroneous natural subtraction in a negative Laurent exponent. |
| `Y`, `M`, `R`, `Q` and Gaussian cancellation, TeX lines 5087–5155 | `GaussianBasic.lean:138`–`159`; `GaussianReciprocity.lean:105`–`113` | The same polynomials. Gaussian binomials are defined by q-Pascal recursion. Cancellation and reciprocity are proved, not external inputs or numerical recurrence assumptions. |
| Full correction, TeX lines 5158–5185 | `CanonicalFullCorrection.lean`; `CanonicalRowSum.lean:213`–`295` | The descending uniqueness proof is applied to actual canonical coordinates. The correction range `range(m-1)` includes precisely ranks `0,...,m-2`. The nonpositive residual condition is derived in the final assembly. |
| Row sum, TeX lines 5255–5273 | `CanonicalRowSum.lean:320` onward; `WebProof.lean:18`–`24` | Same sum of the actual `m` family coefficients. `Fin m` uses `j.val+1`, so the endpoints are exactly `1` and `m`. All three original contribution premises are discharged. |

## Boundary and encoding checks

1. `criticalIndex` uses `Int.toNat`, but `gapFormula_odd` proves the argument
   is nonnegative on `1<=j<=m` and proves `D=2*criticalIndex+1`.
   Thus truncation cannot silently change the critical coefficient.
2. `qGauss(n,k)` explicitly vanishes unless `0<=k<=n`. At corank zero,
   the four-summand count reduces to `[a]_q[s+delta-1]_q`, exactly the
   manuscript's `[a]_q[d-1]_q`. The family boundary `(a,s,beta,delta)=(1,1,0,1)`
   has count one.
3. The natural exponent `n-2h+1` in `Gaussian.difference` is only used
   with `2h<=n` in the cancellation/transition proofs; its truncation
   outside that range is not silently applied inside the main argument.
4. Positive block compositions delete the zero block at auxiliary
   packet size one (`FiniteAuxiliaryBlocks.marked`, lines 28–31). The
   corresponding parabolic equality is proved with a separate `a.val=1`
   branch. The main graph itself requires `m>=2`, so its `m-1` edges are
   positive.
5. Full type with corank one has negative multiplicity allowance and is
   excluded. Full-rank non-family terms are excluded separately. This
   justifies both omitted endpoints of the correction sum.
6. `CanonicalRowSum.coordinate_readout` expands an actual finite-support
   basis coordinate. It does not assume that the six-pattern list is the
   complete expansion. Exhaustion and contributions are proved before
   the readout.

## New independent finite-set experiment

Run:

```sh
python3 scripts/audit_finite_gallery_fidelity.py
```

This script enumerates all actual subspaces of `F_2^5`, obtaining
`1,31,155,155,31,1` subspaces in dimensions `0,...,5`. For **all 20**
nonnegative `3x3` matrices with row sums `(2,1,2)` and equal outer-column
sums, it constructs coordinate flags with that matrix and directly counts
quadruples

```
L <= I <= K <= H,
dim(L,I,K,H)=(1,2,3,4), L<=F, F'<=H, I0<=I, K<=K0.
```

Every one of the four position counts agrees with the manuscript formula;
the total agrees with the independently transcribed Lean polynomial.
Examples at `Q=2`:

| Matrix | Direct count |
|---|---:|
| `B_2=[[0,2,0],[0,1,0],[0,2,0]]` | 189 |
| `A_(2,1)=[[1,1,0],[0,1,0],[0,1,1]]` | 37 |
| `A_(2,2)=[[1,0,1],[0,1,0],[1,0,1]]` | 1 |

The record is `reports/fidelity-finite-gallery.json`. This is an
**experimental semantic check**, not a Lean certificate, a proof for all
ranks, or verification of the flag-to-Hecke literature dictionary. It is
useful because it counts actual finite objects rather than merely checking
that two closed-form degree polynomials agree.

## Precise diagram coverage limit

`WebMasks.stage_boundaries`, `stage_parabolics` and `stage_masks`
(`WebMasks.lean:49`–`73`) compare all seven boundary types with the
parabolics and lattice masks. They do not define an evaluation of a graph
or prove that winding-sensitive graph evaluation gives `Family.raw`.
Indeed the transitive project-import closure of `WebProof.lean` contains
neither `Web.lean` nor `WebMasks.lean`; those are built separately by the
umbrella module.

This is a formalization boundary, not by itself a gap in the manuscript:
the manuscript explicitly supplies the algebraic six-map construction,
and the formal proof uses that construction. Nevertheless, describing the
current result as a formal proof of all the diagrammatic interpretation
would overstate its coverage. A future strengthening would define the
split/merge/rotation evaluation of the concrete graph, preserve its
cyclic order and cut data, and prove its equality with the six-map word.

## Calibration scope

The manuscript derives the full individual seed KL polynomial in its
calibration section. `Normalization.suppliedSeed_full` verifies only the
Laurent normalization of a supplied polynomial. No inspected declaration
identifies that polynomial with the actual KL polynomial. This is openly
recorded in `status.md`, and the final row theorem does not depend on the
supplied seed. Likewise the individual rule `mu_(j;m)=j` remains conjectural.

The conclusions above concern the original formula/argument layer only.
They should not be used to infer that every general assumption in
`WebLiterature` is a faithful or consistent theorem statement. That requires
the separate adversarial framework audit.
