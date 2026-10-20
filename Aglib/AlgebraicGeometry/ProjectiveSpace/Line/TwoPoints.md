# Normalizing two actual points of P¹

Import `Aglib.AlgebraicGeometry.ProjectiveSpace.Line.TwoPoints` and use
`AlgebraicGeometry.Scheme.ProjectiveLine.TwoPoints.normalizePair`.
It takes two actual `Spec k` section morphisms of the existing native
`Scheme.ProjectiveLine.projectiveP1 k`, their original-field structure triangles,
and their inequality. It returns an automorphism in `Over (Spec k)`.

`normalizePair_first` and `normalizePair_second` identify the actual composed
morphisms with evaluation at zero and one in the fixed affine chart. An endpoint
at infinity is allowed. The construction is valid over every field, including
characteristic two.

Coordinates are extracted from the actual sections by the two native affine
charts. An invertible two-by-two matrix induces a homogeneous coordinate
substitution on the same Proj. Pullbacks compose in the reverse matrix order;
`linearSubstitution_comp` and `matrixMap_comp` record this convention. The
endpoint equalities are scheme-morphism equalities, rather than statements
only about underlying points.
