# The actual projective ambient stalk at a generic image

[GenericStalk.lean](GenericStalk.lean) constructs the original local-ring comparison at the image of
an integral scheme's generic point in projective space. The base R is a
domain, the composite to Spec R is dominant, and its actual
`Scheme.functionFieldMap` is finite. These hypotheses suffice; the source
need not be normal or have dimension at most two, and the map to projective
space need not be a closed immersion. The chosen closed immersions in the
normal-surface concentration argument are its current consumer.

`GenericStalkChart` contains a chart index and the original polynomial
map into the source function field, together with the actual structural
coefficient equation and the factorization of the original generic
morphism. `genericStalkChart` constructs this data using
`exists_coordinateChart_factorization_over` and the existing
`coordinateRingEquivPolynomial`. The constructor assumes no chart-prime
maximality, local-ring comparison, dimension formula, or concentration.

The point is the actual image of the zero prime of the source function
field. Its ideal is the original evaluation kernel, and `point_image`
identifies its image under the original open chart with `i(genericPoint X)`.
`ambientPolynomialStalkIso` is the original point-equality transport,
the original open-immersion stalk map, and the native `Spec.stalkIso`.
`polynomialToAmbientStalk` uses precisely the inverse of this composite on
the original polynomial localization map.

`fieldPolynomialMap` extends the original coordinate values through the
original dominant function-field map. Its restriction to polynomials over
R is the original chart map. The prime is its kernel; `fieldPrime_comap`
identifies its contraction with the actual chart point. Finiteness of the
specified function-field map makes this kernel maximal by
`Ideal.isMaximal_comap_of_finiteType_field`; separability is unnecessary.

The original coefficient localization and native localization-at-prime
composition produce `polynomialLocalizationEquiv`. The localization retains
its native scalar action; `fieldLocalAlgebra_algebraMap` identifies its
structural map with the original composite of the two polynomial maps. The complete
`ambientFieldStalkEquiv` is the preceding actual stalk isomorphism followed
by this canonical localization equivalence. Its polynomial-numerator
formula retains the original algebra maps. Native maximal polynomial
height then proves `genericImage_stalk_dimension`: for a coordinate
indexing `iota equiv Fin (n+1)`, the original ambient local ring has
Krull dimension n. This includes n=0.

The construction changes neither the actual source stalk quotient of a
closed immersion nor the ambient differential coefficient. It provides
the generic ambient dimension and its original chart/localization
comparison. Coherent right-adjoint homology, its actual stalk Ext adapter,
constant codimension at all other points, concentration, canonical-module
freeness, trace compatibility, and GR remain separate claims.
