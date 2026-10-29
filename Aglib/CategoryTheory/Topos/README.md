# Ordinary topos interfaces

Etale consumers use the actual `Scheme.EtaleTopos X` and induced geometric
morphism `Scheme.etaleToposMorphism f`, realized in
[`Sites/EtaleTopos`](../../AlgebraicGeometry/Sites/EtaleTopos.lean). The
operational categories, inverse/direct images and adjunction are the original
native sheaf constructions. Sites provide presentations, covering proofs and
local calculations.

[`GeometricMorphism`](GeometricMorphism.lean) supplies one left-exact adjunction,
identity/composition, two-morphisms and native square mates.
[`SheafMorphism`](SheafMorphism.lean) realizes those operations on native
Set-valued sheaves. Their formal adjunction laws apply under their stated
categorical assumptions. [`Grothendieck`](Grothendieck.lean) separately records
the existence of a presentation by sheaves of `w`-small types on one `w`-small
site; it exposes no chosen operational presentation.

[`Point`](Point.lean) uses arrows from the actual terminal object for global
points, with native Gamma and fibre/skyscraper comparisons in their stated
worlds. [`Slice`](Slice.lean) and
[`SlicePresentation`](SlicePresentation.lean) compare the actual slice over a
sheaf with its category-of-elements site. The comparison retains native
restriction maps, coefficient transformations, units/counits and section
values; [`Slice/Grothendieck`](Slice/Grothendieck.lean) supplies the bounded
slice capability under its explicit hypotheses.

Native module-sheaf coefficient actions live in
[`Sheaf/ToposAction`](../../Algebra/Category/ModuleCat/Sheaf/ToposAction.lean).
They use the existing ring and module categories together with the supplied
actual geometric morphism and scalar maps. Each coefficient sector retains
its explicit universe and realization hypotheses. Current consumers include
etale coefficient forgetting, torsor direct images, intrinsic trivialization
and slice-cohomology restriction. The broader migration and deferred higher
foundations are described in the
[refactor plan](../../../docs/design/SHEAF_COHOMOLOGY_SIX_FUNCTOR_REFACTOR_PLAN.md).
