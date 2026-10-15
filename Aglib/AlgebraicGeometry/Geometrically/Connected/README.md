# Connectedness under arbitrary field extension

[CommonOverfield](CommonOverfield.lean) constructs `AlgebraicGeometry.Scheme.Geometrically.commonClosureEmbedding` for an arbitrary field extension `F → K`, with equality of the actual base-field maps. `connectedSpace_of_fieldBaseChange` descends connectedness through the actual projection.

[FieldExtension](FieldExtension.lean) gives `fieldSpec_geometricallyConnected` for any extension of an algebraically closed field and `connectedSpace_fieldBaseChange` for an arbitrary connected scheme over that field. The field extension need not be finite or algebraic; the scheme need not have finite type or fixed dimension. `geometricallyConnected_of_connected_algebraicClosure` detects geometric connectedness from the chosen algebraic-closure base change over an arbitrary field.

Import the two `Aglib.AlgebraicGeometry.Geometrically.Connected` leaves. The proof uses actual pullback isomorphisms and [tensor domains](../../../RingTheory/TensorProduct/README.md) on geometric fibres. The common-overfield/projection results feed the detection endpoint and external geometric consumers, with fields and schemes in the declared universe `u`.
