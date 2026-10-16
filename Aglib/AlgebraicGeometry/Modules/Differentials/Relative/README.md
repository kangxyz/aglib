# Relative differentials over arbitrary scheme bases

`Basic` specializes the sole generic relative differential construction to
the original structure map `f.c` for every scheme morphism `f : X ⟶ Y`.
`relativeDifferentialPresheaf f` is definitionally the native cokernel
construction from `ModuleCat.Differentials.Presheaf.Relative`, and
`relativeDifferentialSheaf f` is definitionally its original module
sheafification from `ModuleCat.Sheaf.Differentials.Relative`.

`relativeDifferentialSheafHomEquiv f M` represents native relative
derivations into every `M : X.Modules`. The native presheaf pullback class
is automatic on scheme opens; no additional right-adjoint hypothesis is
exported. `relativeDifferentialDerivation_d` is the literal original
`toSheafify` formula. The base-section, restriction, descent and coefficient
naturality statements use the original structure maps and module maps.
There is no field, smoothness, Noetherian, finite-type, or quasicoherence
hypothesis in this basic construction or its universal property.

`AffineBase` proves that bridge for every `f : X ⟶ Spec A` and every
coefficient `M : X.Modules`. `affineBaseConstants f` is the actual composite
of `ΓSpecIso.inv`, `f.appTop` and restriction. The induced base-section
derivation on each principal open is zero by the native localization and
formally-unramified Kähler-module theorem; original sheaf separatedness
extends the result to every base open. Neither the source scheme nor the
target module sheaf is assumed affine or quasicoherent.

`affineBaseDerivationEquiv` and its inverse retain the original `d` values
definitionally and commute with original coefficient postcomposition.
`relativeDifferentialSheafAffineBaseIso` compares the same actual relative
sheaf with the original sheafification of native constant-base
`relativeDifferentials'`. Both directions preserve its exact original
`toSheafify` differential. Its intermediate universal comparison reuses
the sole generic construction; it makes no new choice of a differential
object. Empty sources and base identity maps are included.

The affine Spec-map/tilde comparison now consumes this bridge together
with the existing affine Kähler localization theorem. Smooth relative rank,
open/base-change comparisons, the relative canonical line, and its duality
identification remain separate mathematical results. The older field
differential object must be compared through its original universal
derivation rather than replaced by an unrelated choice.
