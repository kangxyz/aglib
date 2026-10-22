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

The incoming [stalk filtration](StalkFiltration.lean),
[finite-length](FiniteLength.lean), [closed residue](ClosedResidue.lean) and
[finite-pushforward](FinitePushforward.lean) leaves use the actual supported
module and its stalks. They retain the stated closed-point, Noetherian,
dimension and finite-length hypotheses; passing to natural or integer lengths
does not supply a missing finiteness premise.

[BoundedDefect](BoundedDefect.lean) gives one positive ideal-sheaf power
annihilating two coherent modules supported on the same closed locus of a
Noetherian scheme. For a map of coherent modules invertible on an actual open
`U`, any ideal sheaf whose support contains the complement of `U` therefore
has one positive power annihilating both the actual kernel and cokernel.
The theorem uses `IsNoetherian X`; there is no flatness or dimension bound.
The [proper-modification comparison](../../../Cohomology/GrothendieckExistence/ProperAlgebraicComparison.lean)
uses this uniform bound on its original algebraic adjoint.
