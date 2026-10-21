# Finite-stage scheme models

Import `Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes`.

`Scheme.exists_model_of_isColimit` starts with the original scheme
`f : X ⟶ Spec c.pt`, an actual colimit cocone of a small filtered diagram
of commutative rings, and the three native hypotheses
`LocallyOfFinitePresentation f`, `QuasiCompact f`, and `QuasiSeparated f`.
It constructs a stage model satisfying the same three conditions and an
isomorphism in `Over (Spec c.pt)` from its literal native base change to
`Over.mk f`. Nonseparated schemes and noninjective stage maps are allowed.

The construction uses compact-open induction on the original scheme.
For the union of a modeled compact open and an affine open, their
intersection is compact by quasi-separatedness. It is modeled as an
actual open on both piece models at one common stage. The identity of
the original intersection is descended as a `Model.Map`, and that same
map becomes an isomorphism after a later base change. Native open gluing
then constructs the model of the union. The comparison-preserving map,
relative gluing, and the actual colimit of the original binary cover
retain the original scheme and its structural map throughout.

The affine object theorem `Scheme.exists_affine_model_of_isColimit` takes a
small filtered diagram of commutative rings, an actual colimit cocone `c`,
and the original affine scheme with its structural map `f : X ⟶ Spec c.pt`.
It assumes `LocallyOfFinitePresentation f` and constructs a stage `i`, an
affine scheme `Xᵢ`, and a structural map `fᵢ` that is locally of finite
presentation, quasi-compact and quasi-separated.

The returned isomorphism is in `Over (Spec c.pt)`, from the literal object
`(Over.pullback (Spec.map (c.ι.app i))).obj (Over.mk fᵢ)` to `Over.mk f`.
Thus it preserves the original structural map, including for an affine
scheme that was not originally presented as a literal spectrum.
`Scheme.exists_spec_model_of_isColimit` is the spectrum version.
`Scheme.exists_common_affine_models_of_isColimit` places finitely many
such affine objects at one common stage. It rebases the actual models along
the chosen transition maps and compares repeated base change using
`Over.pullbackComp` and the actual colimit cocone equations.

The algebraic construction uses the finite relation coefficients of a
presentation, the actual colimit cocone maps, and Mathlib's presentation
model. The tensor comparison is converted using `pullbackSpecIso` and
`pullbackSymmetry`; no injectivity, Noetherianity, properness or smoothness
assumption is imposed.

Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612` represents finite
presentation of scheme morphisms by the three separate conditions
`LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`.
For affine structural maps the last two conditions hold automatically.

`Scheme.exists_common_open_chart_models_of_isLimit` constructs open models
at one common stage for finitely many actual compact open-immersion sources
in the limit chart base changes. It retains each original source scheme,
the actual comparison map to the model, its triangle to the modeled chart,
and the cartesian square over the base cone. In binary gluing, this models
the same original overlap as an actual open on each of the two piece models.

The finite assembly lemmas
`Scheme.exists_common_homs_between_baseChanges_of_isLimit`,
`exists_common_stage_baseChange_map_eq_of_isLimit`, and
`exists_common_stage_isIso_baseChange_maps_of_isLimit` put actual maps,
actual map equalities, and given-map isomorphisms at one common later
stage. They use the native base-change-composition comparison to retain
all original base maps, including for non-thin filtered index categories.
The common-stage isomorphism supplier needs only locally finite presentation
and quasi-compactness of each source structural map; quasi-separatedness is
required only for the corresponding target structural maps.

`Scheme.FinitePresentationDescent.Model` records an actual stage scheme
with all three native FP conditions, the map from the original scheme,
and its cartesian square over the specified base map. `Model.ofOverIso`
constructs this data from an existing literal base-change comparison;
`Model.rebase` uses the literal native pullback and retains the original
source and structural map. `Model.isIso_baseChange_map` verifies that a
stage map representing a specified original isomorphism becomes an
isomorphism after the actual base change. This data does not assume
that every scheme already has a model. `Model.Map` represents a specified
original `Over` morphism by an actual stage morphism and its commuting
triangle. Identity, composition and literal native base change retain that
original morphism. `Model.exists_common_maps` constructs these maps for a
finite original-arrow family at one common later stage, using the explicit
cartesian models already constructed for its objects.

`Model.Map.isPullback` identifies the square between an original arrow and
its modeled arrow as cartesian. `Model.Map.overIso_naturality` states the
compatibility of the literal base-change isomorphisms with that arrow.
`Model.exists_map` is the single-arrow specialization that retains the
specified original comparison.
`Model.exists_common_open_submodels` constructs the actual open submodels
of finitely many specified quasi-compact open immersions. It returns
open stage inclusions as `Model.Map` records, so later native pullbacks
retain the original inclusion and its cartesian comparison.

`Model.ofOpenDiagram` constructs the model of a specified original
colimit from a finite locally directed diagram of actual models. It
assumes a thin finite indexing category, open stage transition maps,
all three FP conditions on component structural maps, an affine stage
base, and a cartesian comparison for each original component. Its result
is an actual model of the original colimit structural map. Compactness
comes from the finite cover; quasi-separatedness follows by refining
the quasi-separated components to affine covers and using their compact
pairwise intersections. The cartesian comparison uses native relative
gluing and the pullback criterion on an open cover. Components themselves
need not be affine, so this construction applies to binary open gluing.

`Scheme.exists_diagram_model_of_isColimit` applies the general object
construction to a finite diagram `Z` with its original structural natural
transformation `t`. The indexing category has finitely many objects and
finite hom sets. It returns one stage, an actual functor to the over
category of that stage base, the three FP conditions on every object,
and a natural isomorphism from the literal base-changed functor to
`Over.lift Z t`. The proof first descends the finite arrow family and
then simultaneously forces all identity and composition equations.
`Model.exists_diagram` is the corresponding constructor when actual
object models have already been supplied.

Finite additional equalities of supplied stage arrows can be imposed
using `exists_common_stage_baseChange_map_eq_of_isLimit`, retaining the
same canonical base-change system and the actual later-stage maps.
The mathematical target is
[Stacks, Lemma 32.10.1, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM).
