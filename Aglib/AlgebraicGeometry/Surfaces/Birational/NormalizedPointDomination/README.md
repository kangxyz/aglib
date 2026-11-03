# Constructed normalized-point domination

[AffineBase](AffineBase.lean) dominates any supplied integral proper
birational model over a normal Nagata domain of dimension at most two
by a constructed finite normalized-point chain. It returns a normal
integral Noetherian terminal, proper dominant maps with original
function-field isomorphisms, and the literal comparison triangle.
Neither source nor terminal regularity is required.

[AdaptedCharts](AdaptedCharts.lean) and
[FiniteNormalization](FiniteNormalization.lean) derive the necessary
normalization finiteness over the original Nagata surface.
[NormalCommonModel](NormalCommonModel.lean) normalizes the schematic
common-open graph component. [Noncollapse](Noncollapse.lean) derives the
proper-image curve embedding from its finite pair.

[SelectedElimination](SelectedElimination.lean) retains one
residue-transcendental fraction in the actual curve DVR and eliminates
the selected curve by strict finite-order decrease.
[CardinalityInduction](CardinalityInduction.lean) decreases the proved
finite contracted-curve count and composes the literal chains.
[Ideal](Ideal.lean) makes the original image of a nonzero ideal locally
rank one on such a chain. Rational domination, completion rationality and
canonical-numerator image constructions use these interfaces under their
additional hypotheses; domination alone does not prove resolution.

Present consumers include [Birational surface maps, common domination and factorization](../README.md), [Rational surface singularities](../../RationalSingularities/README.md).
