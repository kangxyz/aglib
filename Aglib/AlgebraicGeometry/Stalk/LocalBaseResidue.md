# Original residue scalars over a local base

Import `Aglib.AlgebraicGeometry.Stalk.LocalBaseResidue`.
The namespace is `AlgebraicGeometry.Scheme.Hom`.

Let `A` be any commutative local ring, `f : X -> Spec A` an actual scheme
morphism, and `x : X` with `hx : f x = closedPoint A`. No Noetherian, normal,
integral, complete, finite-type or source-closed-point hypothesis is needed.

`closedBaseStalkEquiv f x hx` is the native isomorphism of the **original**
Spec constants followed by the original base germ. Its underlying map is
recorded in `closedBaseStalkEquiv_toRingHom`. Its composite with the original
`f.stalkMap x` is exactly `f.stalkScalar x`, by
`closedBaseStalkEquiv_stalkMap`.

`closedBaseResidueEquiv` applies the native residue-field equivalence to that
same stalk equivalence. `closedBaseResidueEquiv_stalkScalar` proves the whole
original residue square: the original scheme residue map composed with this
equivalence is the native residue map of the original stalk scalar map.
Locality of the scalar map is supplied by the proved closed-base-point lemma,
not by an additional hypothesis or a replacement algebra action.

`stalkScalar_residueMap_finite_iff` transports finiteness in both directions
across precisely this square. It does not assume or prove residue finiteness
without a supplier: a downstream finite-type closed-point theorem can provide
the original scheme-side finiteness. This lower leaf imports no surface or
completion theory and makes no completed-domain or degree claim.
