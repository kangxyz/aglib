# The actual affine Stein factor of a proper morphism

For an actual proper morphism `f : X ⟶ Y`, a locally Noetherian target, and an
actual affine open `V` of `Y`, set

```text
U = f ⁻¹ᵁ V,   R = Γ(Y,V),   A = Γ(X,U).
```

The namespace `AlgebraicGeometry.Scheme.AffineStein` keeps these original
objects and maps:

```text
first f V       = U.toSpecΓ,
finiteMap f V hV = Spec.map (f.app V) ≫ hV.isoSpec.inv.
```

`factorization` proves `first f V ≫ finiteMap f V hV = f ∣_ V` by the original
open-affinization naturality theorem. Thus this is a factorization of the
original restricted morphism through the spectrum of its literal ring of
functions.

`finite_coefficient` proves that the literal ring map `(f.app V).hom` is finite.
Its proof uses the native proper coherent cohomology theorem in degree zero
for the actual structure module, then `moduleH0EquivOfHom` and the original
open's `topIso` to retain the structural scalar map. The intermediate scalar
square is stated explicitly as `structuralCoefficient_square`. The finiteness
supplier requires properness, with no projective embedding as an extra input.

`finiteMap_isFinite` proves the actual second map finite, and `first_isProper`
proves the actual first map proper from the factorization and separatedness of
the second map.

`first_c_isIso` proves that the original structure-sheaf morphism
`(first f V).c` is an isomorphism. This identifies the actual structure sheaf
on `Spec A` with the actual pushforward of the source structure sheaf, with
the original coefficient map. The proof only needs properness and the affine
open for this conclusion; the Noetherian premise is used for finiteness.

The lower theorem `Scheme.isIso_c_toSpecΓ_of_qcqs` applies to every qcqs scheme.
It assembles the native isomorphisms

```text
IsIso (W.toSpecΓ.app (PrimeSpectrum.basicOpen a))
```

on the actual principal-open basis. These maps are the ones already computed
by Mathlib's qcqs localization theorem. The open-scheme version retains the
literal ambient section ring through its original `topIso`.

No integral, normal, reduced, nontriviality, excellence, field or relative
flatness premise occurs. No normalization-finiteness theorem is used. Empty
inverse images and the zero ring remain included. This module makes no claim
about contracted fibres, target regularity, or a global gluing of the affine
factors.
