# Extension of coherent open subobjects

This family uses `Scheme.Modules.Coherent` and the native finite-type quasicoherent category.
The coherent interpretation is guarded by local Noetherianity.

- [Affine](Affine.lean) extends an open finite-type subobject inside a quasicoherent sheaf
  on a Noetherian affine scheme. Its enlargement theorem adds one Noetherian affine chart
  to an existing finite-type region while preserving the original restriction isomorphism.
- [CompactOpen](CompactOpen.lean) performs compact-open induction from an explicit
  one-chart enlargement hypothesis. Compactness of the added open is a premise; the
  whole-scheme conclusion also assumes `CompactSpace X`.
- [Noetherian](Noetherian.lean) supplies the enlargement input and proves extension under
  `IsNoetherian X`. It preserves the actual inclusion and restriction equations and proves
  essential surjectivity of coherent open restriction.
- [Subobjects](Subobjects.lean) extends a coherent open subobject of a fixed coherent
  ambient object. The conditional theorem records quasicoherence of the specified
  pushed-forward cokernel; the locally Noetherian theorem provides it. No whole-scheme
  quasi-compactness premise is needed for this fixed coherent ambient object.

The lower [affine finite-type approximation](../../QuasiCoherent/FiniteType/Extension/README.md)
works over arbitrary commutative rings. [Localization](../Localization/README.md) consumes
the actual extension maps and support denominators.
