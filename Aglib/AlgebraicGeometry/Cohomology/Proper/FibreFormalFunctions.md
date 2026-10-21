# Idempotent images on proper ideal thickenings

`AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions.exists_section_restrict_eq_of_isIdempotentElem`
proves the following native statement. For a Noetherian commutative ring `A`,
a proper morphism `f : X ⟶ Spec (.of A)`, any ideal `I : Ideal A`, and an actual
idempotent `e : Γ(Modules.idealThickeningSpace f I, ⊤)`, there is an element
`a : Γ(X, ⊤)` such that `(Modules.idealThickeningι f I).appTop a = e`.
The representative `a` is arbitrary; it is not asserted to be idempotent.
There is no flatness, Henselian, completeness, effectivity, or supplied tower
hypothesis. The ideal need not be maximal and the base ring need not be local.

The relative two-point finite étale cover represents the given idempotent.
Actual finite étale equivalence along the nilpotent closed immersions lifts its
map to every positive ideal-power thickening. Faithfulness forces compatibility.
The original structure-unit comparisons identify these actual functions with a
compatible family in the native geometric degree-zero cohomology tower.

The stages use `I ^ n`. Coordinate `1` is used for the image argument; coordinate
`0` is supplied by the original transition from coordinate `1`. The proof compares
coordinate `1` back to the original `I`-thickening through its literal transition,
without assuming a dependent identification of the two presentations.

The canonical formal-functions inverse supplies a completed cohomology class.
Only its first quotient coordinate is represented by an original cohomology
class. Native `H⁰` and pullback-unit formulas turn that representative into the
required original global function. No algebraization of the completed class or
idempotent lifting to the original ring is used.

`exists_original_geometric_coordinate` also exposes the general fixed-coordinate
consequence for a proper coherent coefficient. The upper [ordinary-stalk
comparison](FibreFormalFunctions/Stalk.md) owns the canonical additive
ring-stalk/module-stalk comparison, its original germ formula and the
ordinary-stalk/local-`H⁰` equivalence. It proves the image theorem for the actual
`ProperFibreIdempotents.stalkToFibreSections` over every locally Noetherian target.
