# Coherent presentations from an actual projective embedding

`Presentation` takes the actual closed immersion
`i : X ⟶ ProjectiveSpace R ι`, with finite coordinate type `ι`.
The structural map to the affine base is the original composite with
`ProjectiveSpace.toSpec R ι`.

`exists_uniformNegativeTwistEpimorphism` presents an actual affine-locally
finite-type quasicoherent module `M`. For any bound `B`, it produces `N > B`,
a finite index type and an epimorphism from the native coproduct of copies
of `i^* O(-N)` to `M`. That same source is proved finite locally free. This
statement holds over an arbitrary commutative ring.

`exists_coherent_uniformNegativeTwistEpimorphism` gives the coherent-object
case over a Noetherian ring. Local Noetherianity of `X` is derived from its
closed embedding into the given finite-coordinate projective space.

The quotient map is `twistCoproductMap`: the inverse canonical coproduct
comparison, followed by pullback of the proved projective-space quotient
and the original pullback/pushforward counit. The closed counit is a native
proved isomorphism. No regularity or flatness premise is required.

The construction reuses the projective-space producer in
`ProjectiveSpace/TwistPresentation/Epimorphism.lean` and the existing native
closed pushforward, counit and vector-bundle APIs. The focused consumer is
`AglibTest.ProjectiveCoherentPresentation`.
