# Two-field H1 effacement

The `GenericH1ClassEffacement` entry imports the affine, generic and family
interfaces. Its modules follow the construction:

- `Separable` packages the finite-stage field refinement together with the
  original pointed cover and class-zero conclusion.
- `Affine` uses that refinement for the original affine H1 effacement.
- `Generic` combines it with the finite-Galois coefficient presentation on
  the actual generic Cartesian square.
- `Family` constructs that square for the original family and applies the
  generic result. Only the whole generic fibre is assumed affine.

For the generic endpoint, `B` is an arbitrary commutative ring with its map to
the field `K`, and `k` maps to `K`. The morphism `Y → Spec B` is
quasi-compact and quasi-separated. The specified generic square uses an affine,
smooth, geometrically connected relative-dimension-one `k`-scheme and its
rational point. The original coefficient sheaf comes from `Spec B` and is
killed by a positive integer invertible in `k`. The conclusion retains the
original finite field extensions and embeddings, pointed Galois cover, order bound and
literal pullback-zero equation. The class's Ext world `eX` remains independent
of the field-stage worlds `u+2`.

The family endpoint assumes the displayed family is quasi-compact,
quasi-separated, smooth of relative dimension one and geometrically connected;
it constructs the generic square from the original base changes. See the Lean
statements for their exact maps, scalar towers and hypotheses. These are generic
H1 results; they do not assert a nongeneric neighborhood zero, full C3 or C4,
or smooth base change.
