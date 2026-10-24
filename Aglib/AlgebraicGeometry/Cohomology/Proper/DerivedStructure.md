# The original derived structure unit and Leray sequence

The structural section map, installed derived object, literal structure
and pushforward units, and native H0 equations are owned by
[DerivedStructure/Basic](DerivedStructure/Basic.lean). This module imports
that owner and retains the comparisons with original `Sheaf.H`, the
Postnikov and Leray constructions, and the surface consumers.

For the actual ring map `α : A → Γ(X,O_X)`, `moduleDerivedStructure` is the
installed right-derived global-sections object of the original structure
module. `moduleDerivedStructureUnit` is the single of the literal section
map `a ↦ α(a)`, followed by the existing native
`Functor.rightDerivedSingleUnit`. The module does not construct a second
single-unit comparison.

The zero-degree equation uses the native
`rightDerivedSingleUnit_homology_zero` under preservation of finite limits.
It identifies the actual H0 arrow, after the original single and R0
comparisons, with `a ↦ α(a)` on the original section carrier. Global
sections is not assumed exact.

The same equation also holds through the original
`moduleH0EquivOfHom` presentation.
`moduleDerivedGlobalSections_homology_zero_sections` identifies that old
section normalization with the native R0 comparison on every original
homology class, using the supplied resolution augmentation and its
original degree-zero Ext class.
`moduleDerivedStructureUnit_cohomology_sections` applies this square to
the literal structural unit and sends each original scalar to `α(r)`.

For the original proper dominant map `f : X → Spec A`, the Postnikov
consumer assumes a complete Noetherian local domain A of dimension two,
integral X with the explicit source bound `dim X ≤ 2`, normality of Spec A,
and invertibility of the original function-field map. Proper birational
normality identifies the actual H0 arrow. `Proper/FibreDimension` supplies
the upper bound through the original comparison to additive-sheaf
cohomology. The resulting distinguished triangle retains the literal
structural unit, original native H1, and connecting morphism.

For an original proper birational `g : Y → X`, with integral Y and normal
integral X, the analogous structure-module unit defines a native
positive-truncation triangle. Applying the original derived global-sections
functor gives `moduleBirationalLerayTriangle`. Lower t-exactness makes H0 of
its third term zero; the complete-base dimension theorem makes H2 of its
first term zero. The same triangle's degree-one maps therefore form the
actual `moduleBirationalLerayShortComplex`, proved short exact.

The middle comparison is exactly
`moduleDerivedGlobalSectionsPushforwardCompIso`. The edge comparison uses
the actual first-layer theorem, the original truncation projection, and
`rightDerivedSingleHomologyIso` for pushforward. The published
`moduleBirationalLerayMap` and `moduleBirationalLerayEdge` transport these
arrows through the native original `Sheaf.H` linear equivalences. Their
injectivity, exactness, and surjectivity are proved with the unchanged
actions `α` and `g.appTop.hom.comp α`. No arbitrary small replacement of
the original cohomology groups is used.

`moduleBirationalLerayMap_eq_moduleCohomologyMapAlongLinear` identifies
the existing first Leray arrow with the separately defined original
geometric cohomology map for the same structure-module coefficient arrow.
The proof first compares the original degree-zero section maps. The
native coefficient single units preserve the original short-exact
triangles, and the supplied-resolution comparison preserves their
positive connecting maps. The original additive inverse image and
coefficient mates give the corresponding geometric connecting square.
A common flasque effacement then proves equality in degree one. It uses
the product of an injective presentation on X and the pushforward of an
injective presentation on Y, with actual cokernels. No exactness of
pushforward or injectivity of its image is assumed. Both original map
definitions and their scalar actions are retained.

The module assumes no relative higher-direct-image vanishing, does not
split the Postnikov triangle, and does not assert the residue-field Hom
vanishing or a geometric trace identity. Those remain separate consumers.
