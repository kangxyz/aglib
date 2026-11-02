# Quasi-excellent normalization conditions

For an integral Noetherian scheme of dimension at most two, assume genuine
`IsQuasiExcellentRing.{u, 0}` for every nonempty original affine section ring.
This module derives the remaining normalization conditions used by the surface
resolution criterion:

- The singular set of the original generic normalization is finite. The proof
  uses a finite affine cover of the original scheme, the original finite
  normalization map and its section algebras, J-2, and the affine/stalk
  comparison. No global affine base is required.
- At every singular point of that normalization, the original completed stalk
  is both a domain and integrally closed. The actual finite-map dimension bound
  and normality show that a singular stalk has dimension two; the generic
  normalization completion foundation then applies.

Finiteness of the normalization itself is supplied by
[`Normalization/QuasiExcellent`](../../Normalization/QuasiExcellent.md).
The scheme regular-locus arguments reuse
[`RationalDoublePoint/ClosedSingularPoints`](RationalDoublePoint/ClosedSingularPoints.md).
No resolving model, blowup sequence, or resolution-existence theorem is asserted.
The source universe and auxiliary J-2 test universe are explicit and unchanged.
