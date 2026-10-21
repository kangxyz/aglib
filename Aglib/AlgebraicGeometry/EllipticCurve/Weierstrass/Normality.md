# Normality of the literal Weierstrass model over a DVR

`normalStalks_of_generic_discriminant` proves
`Scheme.NormalStalks (scheme W)` for a domain DVR `R`, a specified fraction
field `F`, and `W : WeierstrassCurve R`, assuming only
`(W.baseChange F).Δ ≠ 0`. Here `scheme W` is the existing homogeneous-quotient
projective cubic. The conclusion concerns its actual stalk rings.

The family `IntegralWeierstrassNormality` and its inhabitant
`integralWeierstrassNormality` retain the exact field, algebra, fraction-field,
equation, and discriminant binders of
`R5Lab/AlgebraicGeometry/Curves/LocalModels/CyclicModelComparison/PresentationMaps.lean:539`,
namespace `R5Lab.AlgebraicGeometry.Curves.LocalModels.MinimalPresentationMaps`.
That source file was read with SHA-256
`251e610b94377cf47d990995b052443be401c82e1852c2274eedcc86f9c6c18b`.
The native namespace is `WeierstrassCurve.Projective`; its existing `scheme`
and `Scheme.NormalStalks` replace the original wrappers. The old consumer
`presentation_normal` applies the family to the presentation's own equation
and generic discriminant, exactly as this native family permits. This file
does not modify the old interface or its consumers.

The proof uses the existing open cover by the original affine and infinity
charts. Their rings are domains over any domain by the native Weierstrass
integrality results. Their actual scalar extensions are identified by
`WeierstrassCurve.affineTensorEquiv` and `infinityRingBaseChangeEquiv`.
The generic charts are smooth over `F`, hence normal by the proved
`Scheme.smoothFieldNormality` theorem. The residue charts are domains over
the residue field, including singular residue cubics.

The algebraic step `dvrAlgebra_integrallyClosed` chooses a DVR uniformizer
and proves its image is prime by identifying the quotient with the actual
residue tensor product. The fraction field is the localization away from
that uniformizer, so localization and tensor base change identify the
generic chart with localization away from the prime image. The proved
`IsIntegrallyClosed.of_isLocalizationAway_prime` criterion then gives
integral closedness of each original chart ring. The actual open-immersion
stalk isomorphisms transport these normal domain stalks to the projective
cubic.

No good-reduction, residue-characteristic, perfectness, Henselianity,
excellence, minimality, or representability assumption is introduced. The
lower prime-localization criterion itself requires no Noetherian hypothesis.
This is the surface obligation `S-WEIERSTRASS-NORMAL`; it does not alter the
separately accepted coordinate-comparison files.
