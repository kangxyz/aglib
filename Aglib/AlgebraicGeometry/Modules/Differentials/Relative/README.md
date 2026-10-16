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

[Affine](Affine.lean) proves `relativeDifferentialAffineIso`, which identifies
`relativeDifferentialSheaf (Spec.map σ)` with the actual
`tilde (CommRingCat.KaehlerDifferential σ)` for every map of commutative
rings, in the same native universe. It combines `AffineBase` with the sole
lower `Modules.Differentials.Affine` localization comparison. The
intermediate constant-presheaf comparison is induced by the original
universal derivations, and its sheaf comparison uses the original module
sheafification. The forward and inverse principal-open formulas retain
the actual `d` and `tilde.toOpen` maps. The actual relative differential
sheaf is consequently quasicoherent; no field, Noetherian, smoothness,
finite-type, or quasicoherence premise is required. An independent public
consumer also checks arbitrary coefficient postcomposition, identity
maps and singleton target rings, including their empty spectra.

[Restriction](Restriction.lean) proves the canonical comparison for every
commuting square whose source and base arrows are open immersions. No
cartesian-square, affine, quasicoherence, or smoothness premise is added.
It uses the original universal derivations and native restriction adjunction;
both directions retain the exact original differential formulas through the
original open section isomorphisms. Its native pullback comparison has the
same forward map after the canonical restriction-to-pullback transport.
The source-open comparison and open-base invariance are also exposed
separately, with arbitrary module-sheaf coefficients throughout.

[SmoothRank](SmoothRank.lean) proves
`relativeDifferentialSheaf_hasRank_of_smooth` and
`relativeDifferentialSheaf_finiteLocallyFree_of_smooth` for the actual
`relativeDifferentialSheaf f`, for every `f : X ⟶ Y` over every scheme base
`Y`. The sole premise is the native `SmoothOfRelativeDimension n f`.
The native standard-smooth affine charts supply actual local free
presentations, using the original open-square and affine comparisons.
Their bases come from the sole ring-only
`KaehlerDifferential.standardSmoothBasis` implementation in
`Aglib/RingTheory/Kaehler/StandardSmooth.lean`; the older field-owner name
is a transparent delegate. Empty sources and dimension zero are included,
without a field, Noetherian, quasicoherence, family, or cohomological premise.

General base change, the relative canonical line, and its duality
identification remain separate mathematical results.
The older field differential object must be compared through its original
universal derivation rather than replaced by an unrelated choice.
