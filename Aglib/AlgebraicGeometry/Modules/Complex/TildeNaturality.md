# Original counit homology naturality

Source: [TildeNaturality.lean](TildeNaturality.lean).

`Complex.tildeGlobalSectionsHomologyIso_naturality` preserves the actual affine
counit comparison for every complex morphism and arbitrary complex shape.
The ring is arbitrary and the complex index universe is independent. Both
actual counits must be quasi-isomorphisms; no quasicoherence, boundedness,
Noetherianity or finiteness premise is added.

The proof composes native `ShortComplex.mapHomologyIso_inv_naturality` with
homology of the existing `tildeGlobalSectionsCounit_naturality` square. The
original homology objects and counit maps are unchanged. The closed-adjoint
resolution-independence consumer uses this law with its proved counit
quasi-isomorphisms.

Direct consumers: [AlgebraicGeometry/Cohomology/ClosedImmersion/RightAdjoint/FiniteSource/ResolutionNaturality](../../Cohomology/ClosedImmersion/RightAdjoint/FiniteSource/ResolutionNaturality.md), [AlgebraicGeometry/Cohomology/ClosedImmersion/RightAdjoint/RegularList/Sheaf](../../Cohomology/ClosedImmersion/RightAdjoint/RegularList/Sheaf.md), [AlgebraicGeometry/Cohomology/DirectImage/Affine/Cohomology/CounitNaturality](../../Cohomology/DirectImage/Affine/Cohomology/CounitNaturality.lean).
