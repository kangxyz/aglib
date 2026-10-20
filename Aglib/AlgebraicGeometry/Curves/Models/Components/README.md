# Actual model component geometry

`Spec.ResidueFiber` defines the literal pullback of an actual map
`π : Y ⟶ Spec R` along `Spec.map (IsLocalRing.residue R)`. Its object,
projection, structural map and section are canonical, with both section
triangles. This primitive needs only a commutative local ring.

`SpecialFiber`, `Intersections`, `TwoGon` and `Polygons` transport the original
unmarked nodal constructions through explicit whole-fibre Over-isomorphisms.
The component indices are the actual irreducible-component subtype; polygon
labels are related to it by a proved equivalence. Intersections retain their
original-residue-field maps and actual isomorphisms with `Spec (κ × κ)`.

`Cartier` uses the proved flat-DVR component-kernel supplier to obtain actual
height-one stalk kernels. Regularity and `RegularCodimOneIdealInvertible` are
explicit inputs to invertibility. `CartierUnions` retains the original
avoidance, sum and tensor comparison families.

`NormalDegree`, `TwoGonNormalDegree` and `Polygons` compute degrees of the
actual restricted dual kernel ideals. The principal-fibre, Cartier degree and
proper-curve product-formula inputs remain visible. The minus-two result
requires `1 < n` for indexed polygons.

`Minimality.VerticalContractionExceptionalComponent` remains an unsupplied
universal family. The actual scheme/map comparison criteria in `Minimality`
and `CyclicMinimality` are conditional on it and the displayed regularity,
properness, flatness, dimension and generic-isomorphism conditions. These
leaves provide no existence theorem for regular or minimal models.

The one-gon component is singular. Its normalization is the constructed
projective line, with two actual branches over the node. The length-one
polygon comparison preserves the original three chart maps. Normalization-aware
one-gon minimality and the pointed-cover component/complement assemblies remain
separate downstream boundaries.

The extraction basis is R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, the seven
`LocalModels/Incidence` sources and the explicitly selected unmarked
construction/line/minimality prerequisites. No terminal elliptic/model or
marked polygon records are imported. The focused public client is
`AglibTest.SurfaceComponents`.
