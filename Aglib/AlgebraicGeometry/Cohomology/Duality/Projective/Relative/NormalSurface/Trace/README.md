# Original canonical trace and local evaluation

[Proper](Proper.lean) constructs the ordinary canonical trace on the actual
proper pushforward. Both normal integral surfaces retain their closed
finite-coordinate embeddings over a regular local domain, dimension at
most two, dominant structural maps, finite generic-image maps and original
base triangle. The trace is normalized by the original derived single unit,
global-sections composition and coherent Serre equivalence.

[IsIso](IsIso.lean) proves invertibility of that original trace when the
original derived structure unit is an isomorphism. This is a supplied
vanishing consequence, not a theorem that every proper birational model has
such a unit. [ProperTransposeCoefficient](ProperTransposeCoefficient.lean)
retains the actual coefficients, transpose and derived comparison square.

[BaseChange](BaseChange.lean) expresses the pullback associated to an
invertible ordinary trace as pullback of its inverse followed by the
geometric counit. Its Cartesian identity uses no flatness or properness.
[DegreeZero](DegreeZero.lean), [Localization](Localization.lean),
[LocalEvaluation](LocalEvaluation.lean) and
[AffineEvaluation](AffineEvaluation.lean) identify this mate with the
original stalk/local-spectrum section map for qcqs morphisms and
quasicoherent coefficients; flatness is retained for the base-change
isomorphism. No later stalk is made complete or finite over the first base.

[Generation](Generation.lean) gives original section-surjectivity formulas
for an invertible trace and its flat qcqs base change.
[Restriction](Restriction.lean) proves invertibility of the same pullback
on an original isomorphism open.
[StalkAction](StalkAction.lean) retains the actual source-stalk action,
and [StalkInjectiveDimension](StalkInjectiveDimension.lean) bounds the
injective dimension of the same canonical stalk by its actual local
dimension.

The point-blowup frame, generation and inverse-line interfaces retain
native finite self-injective dimension of the original parent stalk and
generation on the actual full exceptional scheme. Their original global
embeddings, local comparison and residue coefficient line remain explicit.
These conditional interfaces do not supply full rational/Gorenstein
reduction, all-model H1 vanishing or the global trace argument.

Present consumers include [Cohomology of the regular-point exceptional line](../../../../../Blowup/RegularPoint/README.md), [Canonical coefficients on embedded normal surfaces](../README.md).
