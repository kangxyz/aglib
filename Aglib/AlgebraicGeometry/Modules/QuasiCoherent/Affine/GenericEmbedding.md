# Original affine generic and stalk embeddings

Source: [GenericEmbedding.lean](GenericEmbedding.lean).

Let A be a domain object in `CommRingCat`, M an actual module sheaf on
`Spec A`, and eη a specified frame of its actual generic stalk over the
literal native `(Spec A).functionField`. No alternative fraction field,
localized module or stalk model is selected.

`affineSectionsToFunctionField` is exactly the accepted original affine
top germ followed by that same generic frame. Its value law states this
literal formula. The construction needs neither quasicoherence nor
torsion-freeness. Under genuine quasicoherence and torsion-free original
global sections, `affineSectionsToFunctionField_injective` uses the original
germ's module-localization property and native localization injectivity.

For an actual point p, `affineStalkToFunctionField` uses the native
`IsLocalizedModule.mapExtendScalars` on the same original p-germ and the
identity map of the same function field. Quasicoherence supplies the source
module localization. The actual stalk ring acts through its original native
stalk-specialization map to the function field. The A/stalk/function-field
scalar tower is derived from `StructureSheaf.toStalk_stalkSpecializes`,
not assumed by identifying a different top-section scalar action. Local
instance declarations expose these existing maps only.

The section-value and literal germ laws preserve the same selected frame.
The stalk-map injection theorem again requires only quasicoherence and
torsion-free original global sections. There is no finite, Noetherian,
normal, local, dimension or surface hypothesis. No canonical-module theorem
is imported: a later canonical consumer must derive the actual generic
frame and torsion-freeness and transport the original affine chart maps.
The finite embedded-module numerator construction remains a separate native
fractional-ideal consumer.

Direct consumers: [AlgebraicGeometry/Modules/Pullback/LocalSpectrum/GenericEmbedding](../../Pullback/LocalSpectrum/GenericEmbedding.md).
