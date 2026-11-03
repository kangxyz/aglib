# Actual singular child local rings

Source: [BlowupChildren.lean](BlowupChildren.lean).

`singular_stalk_properties_of_rational_model` works on an actual integral
normal proper dominant model f:X→Spec A of a Noetherian Nagata local domain
A of dimension two. The actual function-field map is an isomorphism, and
A satisfies the existing universal `NormalModificationH1Vanishing` predicate.
For an actual singular point x of X, it derives:

- the original stalk is a domain, integrally closed, Noetherian and Nagata;
- its dimension is exactly two;
- x is closed and nongeneric, and f(x) is the actual closed base point;
- the original map `(f.residueFieldMap x).hom` is finite;
- the original stalk has universal normal-modification H1 vanishing.

The residue map is exactly the scheme morphism's own residue map, between
the residue field at f(x) and that at x. The base-point equality is retained
separately. No unrelated field isomorphism, separability or equality of
residue fields is inserted.

Nagata is proved by choosing an actual affine neighbourhood of x, applying
the existing adapted birational chart theorem to the literal original section
map, and localizing that ring at the original point. The base global-section
ring is related to A by the original GammaSpecIso. No completion of the child,
finite A-module structure on it, or coefficient field is assumed.

The global model dimension is derived from the genuine Nagata birational
chart theorem. Normality and that dimension bound make a singular point a
closed dimension-two point. Its nongenericity also follows directly from
regularity of the original generic field stalk. The native rationality
propagation theorem then applies to that actual point and morphism.

`singular_child_properties_of_complete` specializes to the literal ordinary
maximal-ideal blowup of a complete normal rational local surface. It derives
Nagata of the base from completeness and model normality from the existing
ordinary rational-blowup theorem. Its children are not claimed complete or
finite over A. The general model theorem can be reused on later actual
normal proper birational models without reintroducing completeness on their
local stalks.

This closes the normality/domain/Noetherianity/Nagata/dimension/rationality
and finite-residue part of child geometry. Gorensteinness, canonical
trivialization, the Hilbert function, actual quadratic kernels, cubic markers
and termination remain separate obligations. No such conclusion or
conclusion-shaped hypothesis is introduced here.

The general stalk-Nagata theorem is owned by
[Birational/StalkNagata](../../Birational/StalkNagata.md).
This module retains its public wrapper and uses the same
`AffineBaseCharts` input.

Present consumers: [Resolution/RationalDomination](../RationalDomination.md), [CaseOneNonreturn](CaseOneNonreturn.md), [FinitePrefixGeometry](FinitePrefixGeometry.md), [OriginalPathCones](OriginalPathCones.md), [OriginalTripleEntryStep](OriginalTripleEntryStep.md), [PointHeight](PointHeight.md).
