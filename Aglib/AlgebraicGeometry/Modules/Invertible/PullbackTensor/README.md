# Local tensor-pullback comparison

[Local](Local.lean), imported as `Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local`, owns `Scheme.Modules.Invertible.PullbackTensor.Local`. For an arbitrary scheme map, `pullbackTensorMap_isIso` makes the canonical tensor-pullback comparison invertible when the first coefficient sheaf is locally rank one; the second is arbitrary. Flatness of the scheme morphism is not assumed.

The actual comparison is detected on genuine trivializing opens, where it is the unit comparison. `pullbackLineBundleTensorIso` specializes it to two line bundles. `pullbackClass_add` and `pullbackHom` then make ordinary Picard-class pullback additive; the negation formula follows for those same groups.

The lower actual tensor/dual/pullback interfaces are in [Invertible](../README.md), with generic restriction/sheafification in the module-pullback tier. This is the complete ordinary Picard additive-pullback endpoint, not an added global comparison premise.
