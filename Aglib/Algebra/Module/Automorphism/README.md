# Finite projective modules with an automorphism

`Module.Automorphism.Object R` bundles an actual finite projective `R`-module
with an `R`-linear automorphism. Its carrier has the coefficient ring's universe.

- `Basic` supplies intertwining isomorphisms, direct sums, unit objects and the
  tensor product of two one-operator objects. The tensor product lies in
  `Module.CommutingAutomorphisms.Object`: the first operator acts on the first
  tensor factor and the second on the second factor.
- `BaseChange` uses actual tensor scalar extension, with identity, composition,
  direct-sum, tensor and unit comparisons.
- `ScalarGraph` constructs the one-variable Laurent action and the ordered
  right-scalar graph. The first coordinate remains the original operator and
  the second is the chosen scalar. Its support equivalences use actual kernels.
- `ScalarGraphLengths` compares actual localized modules through that surjective
  graph map. The equality holds in `ENat`, including infinite lengths.
- `UnitPath` supplies elementary two-by-two operator paths and their literal
  scalar-extension compatibility.

The modules are native extractions from the corresponding frozen R5 sources at
`f8a3314ddecffcada2ec721d26d56a937bed9690`; each source file records its exact
original path and SHA-256. No K-group, quotient relation or scheme interface is
part of this family.
