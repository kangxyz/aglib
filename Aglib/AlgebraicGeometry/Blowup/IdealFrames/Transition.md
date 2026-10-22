# Original frame maps and pullback coherence

Import `Aglib.AlgebraicGeometry.Blowup.IdealFrames.Transition`. This extends
`Scheme.Blowup.IdealFrames` from the
[actual ideal-frame owner](../IdealFrames.md). Its scheme statements use
arbitrary actual scheme morphisms, module sheaves and displayed frames;
the affine scalar statements use commutative rings and the specified ring
map.

For `f : X ⟶ Y` and an original frame `e : O_Y ≅ M`, `pullbackFrame`
is the inverse native `pullbackUnitIso f` followed by the pullback of `e`.
`pullbackFrame_comp` and `frameAlong_comp` retain the native
`pullbackComp` comparison under composition. `pullbackFrame_hom` and
`pullbackFrame_hom_factor` expose the original forward arrows and preserve
a supplied forward-frame factorization.

For an actual `φ : S →+* T`, `pullbackUnitHom_mul` carries the original
relation `e₁ = affineMultiplication S s ≫ e₀` to the relation with scalar
`φ s`, through that same affine pullback and its native unit comparison.
This scalar transport requires no flatness or regularity hypothesis.

`frameAlong_square` and `frameAlong_ambient_square` retain the actual
commuting chart and ambient squares, their original frame compatibility,
and the native `pullbackComp` and `pullbackCongr` components.
`ambientComparison_congr` compares those same components under the given
map equalities. The categorical `frameAfterMaps` constructs an isomorphism
from a specified frame and specified inverse maps. `transportFrame_hom`
transports the original scalar relation through the displayed comparison
isomorphisms; it does not cancel an ideal inclusion after fibre reduction.

The current [regular-point frame consumer](../RegularPoint/Normal/Frames.md)
supplies the original reciprocal-chart transition from
`chartFrameAfterMap_transition`. Its
[local normal-line consumer](../RegularPoint/Normal.md) closes the actual
`O(1)` conormal and `O(-1)` normal comparisons for a native regular local
ring of dimension two. The generic coherence statements alone do not
identify either projective twist.
