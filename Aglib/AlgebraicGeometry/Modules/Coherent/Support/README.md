# Small presentations of coherent support categories

[SmallModel](SmallModel.lean), imported as
`Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel`, uses the actual open
restriction between coherent categories on locally Noetherian schemes. Its small-model
kernel equals the geometric support condition on the represented object.

The module keeps Mathlib's chosen `SmallModel.{u + 1}` and `equivSmallModel` presentations.
It gives the equivalence between the small support subcategory and the actual supported
coherent category, its exact inclusion, and the exact comparison between the two small
support presentations. The inclusion square is a literal equality of the specified exact
functors. Principal-open support is obtained by applying these same constructions to
`principalOpen R r`.

The generic [small-model interfaces](../../../../CategoryTheory/SmallModel/README.md)
own transported functors and the abelian exact comparison. The
[localization family](../Localization/README.md) owns the ordinary support-quotient theorem.
