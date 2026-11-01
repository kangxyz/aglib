# Torsor constructions on sites

[AdjointPullback](AdjointPullback.lean) constructs the actual torsor action
through a supplied adjunction, using its unit and counit.
[CartesianMaps](CartesianMaps.lean) constructs the existing torsor action from
the original action and difference maps and their finite-product equations.
[RepresentedIso](RepresentedIso.lean) uses a supplied equivariant carrier
isomorphism on the selected represented torsors.

[PointTranslation](PointTranslation.lean) identifies the difference on the
original generalized-point torsor with its positive transporter.
[AffineDisplacement](AffineDisplacement.lean) treats displacement on the
supplied continuous affine torsor; a basepoint is required where used, while
unique transport also applies to an empty carrier.
