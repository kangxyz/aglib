# Actual affine projective embeddings after arbitrary scalar change

[AffineEmbedding.lean](AffineEmbedding.lean) takes the supplied original
`B : BlowupDatum (affineCenter R I)` and an arbitrary `R`-algebra `S`.
The original Rees degree-one irrelevant-ideal theorem supplies the cover
required by `Proj.DegreeOneBaseChange`. The unique comparison with the
original affine Rees blowup then constructs `scalarReesIso`, an actual
isomorphism from `Proj (S ⊗[R] reesAlgebra I)` to the literal pullback of
`B.map` along `Spec S → Spec R`. Both original projections are retained.

For a displayed family `v` spanning the full tensor module `S ⊗[R] I`,
`embedding` applies the actual scalar degree-one monomial map to every
original member. The proved spanning and degree-one power identities,
including degree zero, supply the polynomial graded quotient.
`embedding_isClosedImmersion` proves that the resulting map from the
original literal fibre product is a closed immersion.
`embedding_toSpec` retains the original projection to `Spec S`.
A finite family gives a finite-coordinate standard projective embedding;
closedness itself does not require finiteness of the index.

There is no flatness, domain, Noetherianity or image-ideal replacement
hypothesis. The scalar algebra is the full tensor Rees algebra. It is
not identified with the Rees algebra of the image ideal on `S`.

The next consumer must identify the actual affine row of the global
coherent twist presentation with this displayed tensor family. This leaf
does not assume that identification or prove the global coordinate graph
closed, and it does not assemble projectivity of a point-blowup chain.
