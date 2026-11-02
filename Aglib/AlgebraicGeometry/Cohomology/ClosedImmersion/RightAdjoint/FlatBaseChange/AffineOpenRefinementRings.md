# Mapped ideals in an affine refinement square

Source: [AffineOpenRefinementRings.lean](AffineOpenRefinementRings.lean).

Let `R,S,U,V` be commutative rings in the common geometric universe,
with the four displayed algebra maps and an ideal `I ⊆ R`.
The equality of their two composites `R → V` proves

`(I.map (algebraMap R S)).map (algebraMap S V) =
  (I.map (algebraMap R U)).map (algebraMap U V)`.

`affineOpenRefinement_targetSource_isPullback` retains the original
quotient map into that literal mapped ideal and proves its Cartesian
source square. `affineOpenRefinement_ringSquare_of_isPullback` derives
the required ring equality from the actual ambient Cartesian square.
Commutativity alone supplies no flatness hypothesis.
