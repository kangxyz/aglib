# Reduction of finite etale algebra points

[PointSpecialization](PointSpecialization.lean), in `Algebra.Etale.Reduction`,
constructs point reduction through the actual spectral integer ring and the
chosen residue closure of a complete nontrivially normed ultrametric field.
The specified valuation subring is the norm unit ball. The model is finite;
etaleness gives injectivity by the native local-target unramified rigidity
theorem. The Galois square uses the literal `Valuation.ResidualGalois.absoluteResidue`.

[PointBijection](PointBijection.lean) proves surjectivity by equal finite
geometric-point cardinalities. It retains the actual generic and special tensor
fibers, derives compatibility with supplied multiplication, unit, inverse, and
model maps, and constructs the additive equivalence only from its stated
group structures and compatibility equations.

These are algebraic point comparisons. A good group model, its multiplication
kernel, fiber identifications, and a sheaf or H1 comparison remain inputs at
their geometric consumers. Both sources are from R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, with exact hashes in the leaves.
