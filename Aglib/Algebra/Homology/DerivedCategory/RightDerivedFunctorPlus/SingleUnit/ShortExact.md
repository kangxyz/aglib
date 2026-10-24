# Original derived single units on short exact diagrams

`rightDerivedSingleUnitTriangleMap` takes an actual short-complex arrow
`S ⟶ T.map G` between short exact sequences and uses the literal maps
`single(φ.τᵢ) ≫ G.rightDerivedSingleUnit T.Xᵢ` as all three components.
It reuses the installed native unit.

The first two squares follow from native unit naturality. The triangulated
morphism axiom supplies a third component. Exactness of the source triangle
factors its difference from the specified third component through the first
single shifted by one. That source is strictly negative and the derived
target single is nonnegative, so t-structure orthogonality kills the
difference. The resulting third square therefore concerns the actual
original coefficient unit.

The functor is additive and the source has enough injectives. No exactness
or preservation of injective objects by `G` is assumed. The current consumer
is the original proper-birational Leray map comparison in
`Cohomology/Proper/DerivedStructure`.
