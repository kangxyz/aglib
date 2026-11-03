# Native regular-source pushout comparison

Source: [Pushout.lean](Pushout.lean).

`scalarExtensionPushoutIso` is only the composite of the existing
extendScalarsAlgebraObjIso and Algebra.IsPushout.equiv for the GIVEN rings and
algebra actions. It creates no replacement tensor, quotient, or scalar
base-change mate. Its unit sends the original 1⊗a to algebraMap A B a.

`scalarExtensionPushoutIso_comp` retains the given R→T action and uses the
existing extendScalarsCompOfEq with the actual tower equation. All algebra
and scalar-tower hypotheses are explicit. It derives the composite pushout
from the two actual stage pushouts using Algebra.IsPushout.comp_iff, rather
than assuming a desired composite compatibility. Its proof uses native unit
laws, scalar associator/map laws, and hom_ext on the actual tensor source.
No flatness, Noetherianity, field, or finite-module hypothesis is used.

The intended localization consumer must identify these source maps with the
ORIGINAL canonical quotient and geometric localization constructors by their
proved unit laws and hom_ext. Object isomorphisms alone do not prove that
comparison, own-homology overlap, global canonical gluing, or arbitrary-field
generation.

`scalarExtensionPushoutIso_inv_comp` derives the inverse-source square from
that same forward composition law and native inverse identities. It retains
the given R→T action, scalar associator and internally derived composite
pushout.

Direct consumers: [AlgebraicGeometry/Cohomology/ClosedImmersion/RightAdjoint/FlatBaseChange/LiteralQuotient](../../../../AlgebraicGeometry/Cohomology/ClosedImmersion/RightAdjoint/FlatBaseChange/LiteralQuotient.md).
