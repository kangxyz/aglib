# Ordinary scalar extension for the full Hilbert function

Source: [ScalarExtension.lean](ScalarExtension.lean).

`cmCurve_hyperplanePower_h0_finrank_of_algebraic_extension` works with variable
fields k and K, where K/k is algebraic and K is algebraically closed. It uses
the original chosen projective pullback, not a second fibre model. The inputs
are the actual closed-stalk CM-parameter condition and original-field
`h0(O)=1`, `H1(O)=0`, `H0(L∨)=0`, `h1(L∨)=1`, for `L=j*O(1)`.
Its conclusion is `h0(L^r)=2r+1` for every r over the original field k.

The original ordinary cohomology scalar-extension isomorphism transports
vanishing and rank. The original pullback tensor and unit comparisons give
the inverse-line isomorphism; the actual power-pullback comparison gives the
positive powers. The proved `Geometric` stage constructs a genuine finite
Cartier hyperplane on the full curve over K and computes every rank there.
Dimensions then descend along the same original ordinary cohomology map.
All nilpotents remain; no canonical-module base-change theorem is used.

The final `BaseChange` consumer chooses `K=AlgebraicClosure k`. The present
stage is independently stated for an already supplied extension, so the
chosen closure is not built into its theorem or its original maps. The
canonical geometric source of the inverse-line H0/H1 facts remains a separate
obligation and is not supplied by an assumed Hilbert identity.

## First-power variant

`cmCurve_hyperplanePower_h0_finrank_of_firstPower_of_algebraic_extension`
replaces the inverse-line H0/H1 inputs by the actual first-power equality
`h0(L)=3`. Its other hypotheses and original projective pullback are unchanged.
Only the original unit H0/H1 and positive-line H0 are transported to K; the
existing regular-hyperplane first-power theorem computes all powers there.
The original power-pullback and ordinary cohomology isomorphisms descend every
H0 rank to k. No coefficient canonical module or inverse-line comparison is
needed by this variant.

## Shared vanishing backend

The private `cmCurveCohomology_subsingleton_fieldExtension` retains its exact old telescope and is now a thin call to the unchanged implementation in Generation/VeryAmple. All other scalar-extension proofs/maps are unchanged.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/AnticanonicalHilbert/BaseChange](BaseChange.md).
