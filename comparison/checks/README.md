# Exact spherical Hecke calculations

From this directory, run `python3 compare.py --full 2 3 4` with Python 3.10 or newer. The program uses the standard library. See the [recorded output](results.txt). A printed polynomial is a dictionary of exponent–coefficient pairs in the paper's Hecke variable v. The printed number of canonical summands counts distinct basis vectors with nonzero graded multiplicity.

## Standard coordinates

Encode a spherical minimal representative x by the levels floor((x(i)−1)/N). In each level the window entries increase left-to-right. To recover the residues, assign 1,…,N in decreasing order of level, breaking ties left-to-right. Admissible levels −1,0,1 are the letters A,B,C in the Bowman–de la Fuente–Libedinsky–Plaza paper.

A right finite simple reflection permutes adjacent levels. At s₀ compare the last level with the first level plus one, and exchange these unwrapped levels before restoring the original period. If the levels compared are distinct and in ascending (respectively descending) order, multiplying the corresponding standard basis vector by C_s gives the exchanged vector plus v (respectively v⁻¹) times the original vector. Equal levels give (v+v⁻¹) times the original vector.

The code uses a separate block-orbit algorithm to multiply a vector F by a parabolic symmetrizer C_P divided by the previous overlap factor π_T. Cut the circle at a missing reflection and add one to every wrapped level. For each ordered tuple of sorted position blocks, let L be the stabilizer in W_P, d(x) the total number of within-block inversions in increasing order, and D = ℓ(w_P)−ℓ(w_L). The coefficient at y in this orbit after the operation is

    v^{D-d(y)} (π_L/π_T) Σ_{x in the orbit} v^{-d(x)} [M_x]F.

Indeed M_xC_P = v^{-d(x)}M_min C_P, and parabolic coset decomposition expands M_min C_P with coefficient π_L v^{D-d(y)} at y. The formula applies to the initial affine block by periodicity. Every division in the code checks that the Laurent remainder vanishes.

## Canonical coefficients

`canonical(x)` starts at M_e. Choose any right descent s of x, recursively calculate C_{xs} and multiply by C_s. The result is bar-invariant, monic at x, and all its lower standard coefficients are polynomials. Subtract the constant term at z times C_z for each strict lower z. This gives C_x by bar triangularity. The recursion uses only the Hecke action and canonical triangularity, so it also provides an independent calculation of the seed and the row entries. The separate `canonical_coefficients` routine eliminates from longest to shortest, retaining every Laurent multiplicity.

The program computes the seed C_{X₀} from each construction and compares the two expansions. Compressed averages are over Q₁={2,…,m} and Q₂={1,…,m−1}, dividing at each step by Π_{m−1}. The normalized projector to the V boundary is C_V/π_V, where V=I∩J_m. For the proportionality test the code multiplies by C_V, clears denominators by using the β standard coordinate, and compares every coordinate. The printed minor is $([M_e](FC_V))([M_\beta]A)-([M_e]A)([M_\beta](FC_V))$, evaluated at $v=1$. Equality of the two full vectors with the same multiplicities, proportionality over Q(v), and equality of the identity's degree-one coefficient are distinct tests.

The recorded calculations give the multiplicities for each truncated product BS_j in the ranks tested. The [partial-row argument](../report/partialrows.tex) treats the cumulative canonical summands for general m.

## Partial-row check

Run `python3 partial.py 2 3 4 5` to reproduce the [partial-row output](partial-results.txt). This compares all admissible type-r full-spherical coefficients of the raw gallery BS_j with a separately evaluated smaller-rank gallery, computes the cumulative canonical preimage using ordinary KL recursion, and verifies that their difference on these coordinates has no terms below v^5. It checks all predicted family-F and full-spherical canonical multiplicities of the cumulative elements through m=4, the corrected origin coefficients through m=5, and the ordinary KL row entries independently through m=5.
