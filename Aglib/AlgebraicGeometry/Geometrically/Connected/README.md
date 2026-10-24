# Connectedness under arbitrary field extension

[CommonOverfield](CommonOverfield.lean) constructs `AlgebraicGeometry.Scheme.Geometrically.commonClosureEmbedding` for an arbitrary field extension `F → K`, with equality of the actual base-field maps. `connectedSpace_of_fieldBaseChange` descends connectedness through the actual projection.

[FieldExtension](FieldExtension.lean) gives `fieldSpec_geometricallyConnected` for any extension of an algebraically closed field and `connectedSpace_fieldBaseChange` for an arbitrary connected scheme over that field. The field extension need not be finite or algebraic; the scheme need not have finite type or fixed dimension. `geometricallyConnected_of_connected_algebraicClosure` detects geometric connectedness from the chosen algebraic-closure base change over an arbitrary field.

Import the two `Aglib.AlgebraicGeometry.Geometrically.Connected` leaves. The proof uses actual pullback isomorphisms and [tensor domains](../../../RingTheory/TensorProduct/README.md) on geometric fibres. The common-overfield/projection results feed the detection endpoint and external geometric consumers, with fields and schemes in the declared universe `u`.

Focused interface guides: [A rational point on a connected smooth proper curve](PointedCurve.md).

[RationalPoint](RationalPoint.lean) proves the rational-point case of Stacks 04KV with no finiteness
or separation hypothesis: a connected scheme `q : Y ⟶ Spec k` with a section `o`, `o ≫ q = 𝟙 _`, is
geometrically connected (`geometricallyConnected_of_connectedSpace_of_section`). Over every integral
extension `K` the base change `Y_K` is connected (`connectedSpace_pullback_of_section`), and for
every field extension the fibre of `Y_K ⟶ Y` over the rational point has at most one point
(`subsingleton_preimage_of_section`). The projection is universally open and universally closed, so
the images of a clopen partition both contain the rational point; the detection endpoint is
`geometricallyConnected_of_connected_algebraicClosure`. This route differs from the Stacks proof (a
separable algebraic closure, Stacks 056R and 0387). Consumer:
[Group/IdentityComponent](../../Group/IdentityComponent/README.md).
