# Topological sheaves and dimension

[Sheaves](Sheaves/README.md) works on actual topological sheaves, stalks and opens. Main results are basis detection of exactness/acyclicity, actual Mayer–Vietoris sequences, Noetherian-space filtered-colimit sheafification and closed-support comparison without Noetherianity.

[KrullDimension](KrullDimension/README.md) proves that a closed subset avoiding all component generic points lowers a finite topological dimension bound in a quasi-sober space. Its separate disjoint-neighborhood auxiliary lemma retains Noetherianity.

These subjects precede scheme-specialized module and cohomological-dimension arguments. Native declaration owners include `TopCat.Sheaf` and `TopologicalSpace`; source imports use `Aglib.Topology`.

[Semicontinuity](Semicontinuity.lean) proves that two upper semicontinuous
natural-valued functions with locally constant sum are individually locally
constant. It is the pure numerical input for the reduced local Grauert
criterion on original module-complex homology.

[NoetherianSpace](NoetherianSpace.lean) proves that on a Noetherian space any
family of locally constant functions, indexed by an arbitrary type, is jointly
locally constant (`TopologicalSpace.NoetherianSpace.isLocallyConstant_pi`), and
Noetherian induction for finite images
(`TopologicalSpace.NoetherianSpace.finite_range_of_isIrreducible`): if every
irreducible closed subset meets an open set with finite image, the function has
finite range. `TopologicalSpace.NoetherianSpace.exists_forall_le_of_isIrreducible`
derives from it a uniform bound `N` for an eventual property `∀ d ≥ N, P x d`
from bounds on a nonempty open part of every irreducible closed subset. Its
present consumers are the fibre Hilbert polynomial leaves
`Cohomology/Projective/HilbertPolynomial/FlatFamily` and
`Cohomology/Projective/HilbertPolynomial/Finiteness`, and the large-twist fibre
statements `Cohomology/Projective/FiberBaseChange`.
