# The bundle of an extension of the structure module

Import `Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension` and use
`AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension`.

The input is the original pair of module-sheaf maps
`i : O_X → E` and `g : E → O_X`, their zero composite, and short exactness of
that actual short complex. The base is an arbitrary scheme. There is no
Noetherianity, reducedness, affineness, or global splitting hypothesis.

An `AffineFrame g` is an original affine open together with a section of `E`
whose image under `g` is one. Epimorphy supplies such frames locally. Their
opens form a basis, and `frameCover` is an actual locally directed open cover.
For an inclusion of two frame opens, `transition` is the unique original
scalar satisfying `i(t) = restricted_lift - lift`. The theorem
`transition_spec` retains that exact original section equation;
`transition_comp` proves the additive cocycle using original restrictions.

`chartFunctor` uses the existing native projective line over each frame's
ring of functions. Its arrows are the original unipotent matrix maps followed
by the original coefficient restrictions. `chartMap_isPullback` proves the
actual cartesian chart square. `gluingData`, `projectiveBundle`, and
`projection` construct the scheme and structural map using native relative
gluing; `projection_isProper` proves properness locally on the original base.
No desired bundle or gluing-existence hypothesis is an input.

`chartInclusion` retains each original colimit map, with its open-immersion,
projection-triangle and cartesian-square theorems. `quotientSection` glues the
literal infinity section of those charts; `quotientSection_chart` and
`quotientSection_projection` retain the exact original local and base
triangles. Properness of the projection makes that section a closed immersion.

The construction is being extended with its actual trivial conormal, affine
complement, and the original complementary section on a supplied split open.
These are not consequences claimed by the current bundle-and-section endpoints. The later finite normalization of the
section closure in Stacks 0AXB remains a separate obligation; this file does
not assert punctured H1 injectivity or surface resolution.

`quotientSection_chart_isPullback` supplies the cartesian square of the
original section on each frame. The `RankTwoExtension.Complement` and
`RankTwoExtension.Conormal` children develop its actual complement,
split-open complementary section, ideal and local conormal frames.
The global trivial-conormal compatibility remains explicitly separate.
