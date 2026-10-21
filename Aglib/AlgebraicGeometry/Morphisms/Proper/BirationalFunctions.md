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

The original connectedness target is the stronger
`ProperBirationalGeometricallyConnected` family in the frozen R5
`Morphisms/Proper/BirationalInterfaces.lean`. The present functions result supplies
a lower obligation. Geometric connectedness of the actual fibres still needs a
valid Stein or other fibre theorem; no H0 base-change premise is inferred here.
Native compiler outcomes are recorded separately from this source interface.
