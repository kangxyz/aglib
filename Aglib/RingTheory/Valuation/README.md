# Residual Galois maps of complete normed fields

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
