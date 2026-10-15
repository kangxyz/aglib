# Actual tensor stalks and pure-germ formulas

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Basic`, identifies the actual module stalk of the sheafified tensor with the scalar tensor product over the original local ring. [Pure](Pure.lean) and [Bilinear](Bilinear.lean) construct the pure-germ/bilinear comparison; [Map](Map.lean) and [Naturality](Naturality.lean) retain the original coefficient-map and section/germ formulas.

The scheme, point, module sheaves and local scalar action are actual objects. These comparisons require no curve, Noetherian or finite-local-free hypothesis merely to define the tensor stalk. Exactness or injective-preservation results introduce their own coefficient conditions later.

The five focused leaves feed tensor hom-extensionality, local exactness and [projection-formula stalk detection](../../ProjectionFormula/README.md). A formula on pure germs identifies the canonical map; it is not an alternative unspecified tensor construction.
