# Additional views of the actual closure and root maps

`ClosureAlgHom.lean` exposes `FieldEmbeddingBaseChange.closureAlgHom`, the
algebra-homomorphism view of the existing chosen `closureEmbedding`. It preserves
the actual field map and the source algebra structure.

`RootCoefficientAction.lean` transports the existing absolute-Galois root action
through the actual field fundamental-group equivalence. Its
`RootCoordinates.arithmeticRootAction` acts on the existing `RootModule`, and
`rootCoordinate_equivariant` identifies its coordinates with the actual
arithmetic cyclotomic character. The characteristic-zero field and nonzero
level hypotheses are retained. No new root carrier or fundamental group is defined.
