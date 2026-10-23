# Actual scalar base change of Proj on a degree-one cover

[DegreeOneBaseChange.lean](DegreeOneBaseChange.lean) uses an actual
commutative graded `R`-algebra `D`, its natural-number grading `G`, an
arbitrary commutative `R`-algebra `S`, and a specified family in `G 1`
whose ideal span contains the original irrelevant ideal. The family need
not be finite. No flatness, domain, Noetherianity or projectivity
hypothesis is imposed.

The native graded coefficient map is the original inclusion
`D → S ⊗_R D`. Its irrelevant-ideal condition is proved, and its native
`Proj.map` is `AlgebraicGeometry.Proj.DegreeOneBaseChange.scalarMap`.
The coefficient maps through the actual degree-zero rings are retained.
No identification of the degree-zero rings with `R` or `S` is assumed.

On every original degree-one chart, the native homogeneous-localization
map is identified with the constructed scalar-extension equivalence on
`1 ⊗ x`. Transport of the native tensor-product pushout gives the exact
chart-ring pushout, and hence the spectrum pullback. The original
`awayι` square is cartesian from its native basic-open preimage equation.
The existing source-open-cover theorem glues these original squares.

`baseChangeIso` is the actual isomorphism

    Proj(G_S) ≅ Proj(G) ×_(Spec R) Spec S.

Its first projection is the original graded-coefficient Proj morphism;
its second projection is the original structural map to `Spec S`.

The current Rees consumer supplies the degree-one cover from the proved
`reesAlgebra.irrelevant_eq_span_degreeOne`. Transport of the original
affine blowup representative and comparison of its actual tautological
quotient remain separate geometric steps. This leaf supplies neither a
standard projective embedding of a point-blowup chain nor a surface
projectivity oracle.
