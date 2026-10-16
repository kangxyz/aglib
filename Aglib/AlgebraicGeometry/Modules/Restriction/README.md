# Ordinary open restriction and sheafification

[Sheafification](Sheafification.lean), imported as `Aglib.AlgebraicGeometry.Modules.Restriction.Sheafification`, owns `Scheme.Modules.restrictionRingHom` and its invertibility for an actual open immersion, together with `restrictionSheafificationIso`, `isIso_sheafified_restricted_unit` and `isIso_restricted_unit_of_iso_sheaf`. All maps are the original structure-ring morphisms and sheafification units; the last criterion retains its supplied actual sheaf isomorphism.

The construction uses the canonical generic sheafification/direct-image comparison. It requires no tensor or rank-one coefficient hypothesis. [Scheme tensor restriction](../Tensor/Restriction.lean) and [line-tensor sheafification](../Tensor/Sheafification.lean) are higher consumers.

[Monomorphisms](Monomorphisms.lean), imported as `Aglib.AlgebraicGeometry.Modules.Restriction.Monomorphisms`, preserves monicity through the actual pullback along an open immersion. [Unit](Unit.lean) records the actual restriction/pullback unit comparison with the canonical unit-to-pushforward-unit map. These lower interfaces do not depend on ideal modules.

[Isomorphisms](Isomorphisms.lean), [Overlap](Overlap.lean) and
[ZeroMorphisms](ZeroMorphisms.lean) give ordinary module restriction interfaces: isomorphisms
on smaller opens and open ranges, the comparison on the same chosen pullback, and zero-map
detection for a target in the actual open direct-image essential image.

These maps feed [preservation of injectives by open restriction](../../Cohomology/Injective/README.md), local basis/presentation transport and the canonical [open-base-change](../BaseChange/README.md) comparison. Open immersion is a geometric input; no Noetherian or finite-type hypothesis is imposed merely to define the functors.

[ExtensionByZero/ClosedImmersion](ExtensionByZero/ClosedImmersion.lean)
gives the original exchange of closed pushforward with genuine open
extension by zero, with its exact unit and all-module stalkwise
invertibility. Its [focused guide](ExtensionByZero/README.md) records the
closed-right-adjoint open-locality consumer.
