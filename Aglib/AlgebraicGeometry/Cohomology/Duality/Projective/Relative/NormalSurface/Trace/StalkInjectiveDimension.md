# Finite injective dimension of the original canonical stalk

Source: [StalkInjectiveDimension.lean](StalkInjectiveDimension.lean).

At every original point x, the statement constructs its actual local dimension
r≤2 and proves injective dimension at most r for the original canonical stalk,
as a module over the original stalk ring. Projective embedding, normal integral
surface bounds, dominant structural map and generic finiteness are retained.

The proof chooses an actual native polynomial chart and quotient-chart point,
retaining its original source-point equality. The ambient stalk is regular,
the source stalk is normal and Noetherian, and the actual dimension formula
is dim ambient=n+dim source. The original polynomial coefficient stalk frame
trivializes the ambient line. The lower concentrated-derived-coinduction / Baer
theorem then bounds injective dimension of the actual source homology.
StalkAction and the actual open-stalk ring isomorphism transport the bound to
the original global canonical stalk. No later stalk is made complete or finite
over the original regular base.
The original canonical-stalk frame criterion uses this bound separately;
this injective-dimension theorem does not itself choose a canonical frame.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/StalkGorenstein](../StalkGorenstein.md).
