# Valuations and residual Galois maps

[ResidualGalois](ResidualGalois.lean), in `Valuation.ResidualGalois`, constructs
the spectral valuation on the algebraic closure of a complete nontrivially
normed ultrametric field. The specified base valuation subring must be exactly
its norm unit ball.

The actual integral-closure equivalence, algebraically closed residue field,
chosen compatible residue-closure equivalence, reduction map, and continuous
absolute Galois residue map are constructed. Surjectivity of the residue Galois
map retains the separate `PerfectField K` hypothesis. Independence of the
chosen residue-closure equivalence is not asserted.

[ResidualInertia](ResidualInertia.lean) identifies the kernel of this same
residue map with literal integral-closure inertia at the transported maximal
ideal. The complete normed field hypotheses and actual reduction map are
unchanged.

The current consumers are [finite etale point reduction](../Etale/Reduction/README.md)
and coefficient/root specialization. Abstract Milnor K residue-data aliases are
already owned by `MilnorK.K2.Specialization` and are not duplicated here.
Both sources come from R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`;
each leaf records its exact source hash.

## Finite orthogonal families

[Sequences](Sequences.lean) defines convergence, Cauchy sequences and
sequential completeness for the actual valuation. For a valuation with value
group `ℤᵐ⁰`, [Orthogonal](Orthogonal.lean) constructs a finite orthogonal basis
of each finitely generated span over a sequentially complete coefficient
subfield, using best approximations. [LeadingResidues](LeadingResidues.lean)
and [LeadingRelation](LeadingRelation.lean) obtain Frobenius independence
from normalized orders and the literal valuation-ring residue maps.

[ParameterMonomials](ParameterMonomials.lean) uses sequential completeness of
the source valued field, a valuation-preserving field map, a normalized
uniformizer, unit-valued parameter lifts and their actual coefficient and
variable residue squares. When the target residue field is the specified
rational fraction field, finite independent source coefficients times distinct
parameter monomials with exponents below the positive exponential
characteristic remain independent over the target's literal Frobenius range.
[IntegerMap](IntegerMap.lean) is the induced map of valuation rings. The
[parameter-DVR completion stability theorem](../DiscreteValuationRing/ParameterCompletionStability.lean)
uses these finite-family results without a global p-basis or a finite
imperfection-degree assumption.
