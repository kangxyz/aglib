# Functions under a proper birational morphism

`BirationalFunctions.lean` constructs the actual structure-sheaf map isomorphism
`IsIso f.c` for a proper dominant morphism of integral schemes onto a target with
`NormalStalks`, assuming the actual `functionFieldMap f` is an isomorphism.

The affine proof uses the native
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`, the injective actual
generic germ maps, their compatibility with `f.app`, and integral closedness of
the target affine section ring in its actual function field. The argument also
works for universally closed morphisms; local Noetherianity is unnecessary.
The sheaf statement follows on the original affine-open basis.

- `bijective_app_of_isAffineOpen_of_universallyClosed_birational`: the original
  section map on every actual affine open is bijective, including the empty open.
- `isIso_c_of_universallyClosed_birational`: the original map from the target
  structure sheaf to the ordinary pushforward is an isomorphism.
- `isIso_c_of_isProper_birational`: the proper-morphism specialization.

[ConnectedFibres](ConnectedFibres.md) proves the stronger native endpoint
`geometricallyConnected_of_isProper_birational`. It retains integral source and
target, properness, dominance, `NormalStalks` of the target and invertibility
of the same actual `functionFieldMap`, and additionally assumes the target is
locally Noetherian. It applies the general theorem for proper surjective `f`
with `IsIso f.c`, whose proof uses the proper affine idempotent-image theorem
and actual flat base change. The functions theorem above still needs no
Noetherianity. No Stein family or nonflat H0 base-change isomorphism is added.

For a Noetherian target of dimension at most two, the separate
[surface isomorphism-locus theorem](../../Surfaces/Birational/README.md)
gives the maximal actual isomorphism open with finite closed-point complement.
Neither endpoint supplies a contraction or point-blowup factorization.
