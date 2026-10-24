# Genuine module coefficients and their original comparisons

This family uses the actual `SheafOfModules` category for the constant ring
sheaf on the small-etale site. The standard scalar and value universe is
`u+1` for schemes in `u`; no torsion, Noetherian, or base-invertibility
hypothesis belongs to these ordinary constructions.

`Underlying` compares the original native module inverse image with the
original abelian inverse image after forgetting scalars. `AdjunctionUnderlying`
retains the unit equation for module-valued sheaves. `NativeAdjunctionUnderlying`
proves that the same native inverse-image comparison preserves the original
module and abelian adjunction units and that its inverse has the original
direct-image comparison as its mate. It does not replace the specified
comparison by a newly chosen isomorphism. The proof uses the native
sheafification counit and equivalence triangle identities.

`ClosedExactness` supplies the exact underlying-sheaf functor. Exactness does
not assert that this functor preserves injectives. The separate
`Derived/UnderlyingAcyclic` consumer proves the relative acyclicity needed for
the original derived direct-image comparison, and `Derived/Underlying` retains
both original composite-unit equations. Exchange compatibility and proper
base-change invertibility are distinct further interfaces.

`UnderlyingComposition` proves the original inverse-image comparison's
composition and equality-transport equations, then proves the full source cube
as equality of the two whole natural-isomorphism chains. All four scalar
comparisons, both original inverse-image squares, and the literal equality of
base-map composites are retained. No cartesianness, properness, or exchange
invertibility is assumed. The derived consumer evaluates this whole cube only
through the abstract exact-localization interface.
