# Coherent Serre transposition of an actual coefficient arrow

Source: [ProperTranspose.lean](ProperTranspose.lean).

`ProperTranspose.lean` uses the existing own-homology canonical modules on
integral normal dimension-at-most-two schemes with closed projective embeddings
over one regular local domain. Both structural maps are dominant and both actual
`genericImageBaseMap` maps are finite. The original structural triangle is retained.

For an ordinary coefficient sheaf `LY` that is quasicoherent and affine-locally
finite type, an actual derived arrow `Psi : Rb_*(LY[0]) → LX[0]`, and an ordinary
`phiX : LX → omegaX`, the construction is

    phiY = EY.inverse(C.hom ; RΓX(Psi) ; EX(phiX)).

`C` is the original global-sections composition with only the scalar equality
forced by the triangle. No proper exceptional inverse image is used. The defining
normalization, original coefficient-functional formula, source precomposition,
and structural-unit/section equations are exposed. The forward `EX` needs no
coherence premise; the inverse `EY` retains the actual coherent-source premise.

The one-pole producer must supply its geometric `Psi`; this file does not supply
that map, its image containment, or a derived proper counit identity by cancellation
after global sections. The one-pole canonical coefficient construction
uses this proper transpose with its supplied geometric arrow.

Source provenance: D `authors/resolution_homcomplex_finish/b7-finite-global-next/
proper-transposition/ProperTranspose.lean`, SHA256 `7dcd0e60eec4edfe62f50cfb7db337418fe3fa01810a937740685274192494e0`.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/Proper](../Trace/Proper.md), [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/ProperTransposeCoefficient](../Trace/ProperTransposeCoefficient.md).
