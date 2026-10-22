# Finite-presentation descent

These modules retain the original objects, structural maps and native
pullback comparisons over an actual filtered colimit of rings.

| Module | Actual construction |
| --- | --- |
| [Diagrams](Diagrams.md) | Canonical scheme base-change systems, their limiting cones, and common later stages for finite families of maps and equations. |
| [Gluing](Gluing.md) | Quasi-compact open models, finite open gluing and eventual isomorphisms of the specified stage maps, with quasi-separatedness required only on the target for eventual isomorphisms. |
| [Schemes](Schemes.md) | Every finitely presented qcqs scheme has a stage model; a finite category of such schemes has an actual stage functor and pullback natural isomorphism. |
| [Properties](Properties.md) | Actual schematic-image, standard-smooth and relative-dimension suppliers for finite-base curve models. |
| [Module maps and properties](Modules/README.md) | Actual global Hom and equality descent for finitely presented module sheaves, with eventual isomorphisms and rank-one frames on the original later pullbacks. |

Scheme finite presentation uses the native three conditions
`LocallyOfFinitePresentation`, `QuasiCompact` and `QuasiSeparated`.
The object and diagram theorems impose no separatedness, Noetherianity,
flatness or injectivity condition on the stage maps. Finite diagram descent
requires finitely many objects and finite hom sets, and retains every
identity and composition equation.

The comparison-preserving `Model.Map` interface represents a specified
original arrow. The binary open-gluing proof uses it to descend the identity
of the original overlap. The separate eventual-isomorphism existence theorem
suffices when only properties are transported between two given models.

[SpreadingOut](../../Morphisms/SpreadingOut.md) constructs finite integer-base
models of actual smooth proper field curves and restores their properties
on later literal base changes of a supplied stage model. Its generic-open
geometric-integrality supplier retains the smooth relative-curve scope.

## Separated models and actual section descent

[SeparatedModels](SeparatedModels.lean), imported as
`Aglib.AlgebraicGeometry.Descent.FinitePresentation.SeparatedModels`, proves
`Scheme.exists_separated_model_of_isLimit`. For a small cofiltered scheme
diagram with affine transitions and qcqs stages, a specified limiting cone
`c`, and a separated `f : X ⟶ c.pt` with
`[LocallyOfFinitePresentation f] [QuasiCompact f]`, it returns a stage `i` and
`M : FinitePresentationDescent.Model (c.π.app i) f` with `IsSeparated M.f`.
The schemes, index and hom universe are `u`. The model's `rawIso` compares the
original source with the literal base-first pullback, and
`Model.rawIso_hom_fst` retains the original structural map. This interface is
consumed by [compactification over Noetherian limits](../../Compactification/NoetherianLimit.lean).

[Sections](Sections.lean), imported as
`Aglib.AlgebraicGeometry.Descent.FinitePresentation.Sections`, provides
`AlgebraicGeometry.exists_common_appTop_π_eq_families_of_isLimit` for finite
families of sections of qcqs affine-transition limits. It returns one common
stage and section lifts with the equation
`s a k = ((c a).π.app i).appTop (t a k)`.
`exists_common_appLE_eq_families_of_isLimit` retains the corresponding
`appLE` maps on inverse images of specified stage affine opens. The finite
family and section-index types have independent universes.

[ProperSubalgebraModel](ProperSubalgebraModel.lean) and the
[residue-stage comparison](ResidueStageComparison.lean) supply the arithmetic
models and original closed-fibre projection equations used by the
[proper henselian comparison](../../Morphisms/FiniteEtale/ProperHenselian/README.md).
The [finite-type descent family](../FiniteType/README.md) separately owns
eventual closedness and the two forms of separatedness descent.
