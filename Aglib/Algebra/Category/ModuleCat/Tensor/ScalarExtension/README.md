# Scalar-compatible tensor transport

Import `Aglib.Algebra.Category.ModuleCat.Tensor.ScalarExtension.FirstVariable`
for naturality of the existing scalar-compatible tensor isomorphism in the
module being extended. Both rings and module carriers retain the universe of
the original `Tensor.ScalarExtension` interface. No flatness, finite generation
or projectivity hypothesis is imposed.

`ModuleCat.scalarExtensionTensorIso_naturality_left` retains the literal
extension of the original coefficient map and both original tensor maps.
`scalarExtensionTensorFirstVariableNatIso α T` packages these same components
as a natural comparison from extension, tensor-right by `T`, and restriction
to tensor-right by the restricted `T`. Its component is exactly
`scalarExtensionTensorIso α E T`; the original pure-tensor and unit inverse
formulas are unchanged.

The geometric consumer is relative flatness of a module sheaf: after ordinary
pullback and tensor-stalk comparisons, this natural isomorphism identifies
the restricted source stalk tensor with tensor over the base stalk ring.
The leaf passed individually through the shared guarded wrapper, receipt
`1792090106587567000-87892`.
The external `work/proper-validation/ScalarTensorFirstVariableConsumer.lean`
checks coefficient naturality and the unchanged scalar pure-tensor component;
it passed with receipt `1792090150281959000-89510`. The inspected declarations
use only `propext`, `Classical.choice` and `Quot.sound`.
