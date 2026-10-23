# Actual line-source projective maps in a pulled frame

[Pullback.lean](Pullback.lean) starts with the actual line-source family
`d i : D ⟶ J`, a scheme morphism `g`, and a specified frame of the actual
pulled source `g*D`. The original source line is locally rank one.

`pulledDualTensorIso` uses the native canonical tensor pullback map.
`pulledEvaluationIso` pulls the original dual evaluation through that
comparison and the native unit comparison. Together with the specified
source frame, it constructs `pulledCoefficientIso`, an isomorphism from
the actual module `g*(Dᵛ ⊗ J)` to `g*J`.

`pulledSection_trivialized` proves that every original pulled coordinate
maps to `eD.inv ≫ pullback.map (d i)`. The evaluation and frame are the
actual maps in that equality. No comparison of a pulled dual with a newly
chosen dual, scalar normalization datum, or flatness premise is supplied.

For an epimorphic finite original row and locally rank-one target,
`mapOfFamily_pullback_eq_of_sourceIso` identifies the actual pulled
projective morphism with the finite-family morphism of that same original
row in the specified pulled frame. Generation of the pulled row is proved
using preservation of coproducts and epimorphisms.

The current consumer is the affine comparison of the original common-twist
presentation on a literal base-changed blowup. This result changes neither
the coordinate index nor the original structural map. It does not assert
closedness of the projective map or projectivity of a surface.
