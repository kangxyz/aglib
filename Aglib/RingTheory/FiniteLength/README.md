# Finite length from maximal support

[Support](Support.lean), imported as `Aglib.RingTheory.FiniteLength.Support`, exports `Module.finiteLength_of_support_maximal`. A finite module over a Noetherian commutative ring has finite length when every prime in its actual support is maximal. No local-ring hypothesis is required.

The argument uses the quotient by the actual module annihilator. The explicit finite-generation and Noetherian hypotheses matter; a mere support condition on an arbitrary module is not this result. Prime-filtration and scalar-homology support calculations are consumers, through the actual `Module.length` interface.

`FiniteAlgebraFiber` constructs the actual closed-fibre finiteness, residue
quotient equivalences and residue degrees for a module-finite algebra over a
local ring. `FiniteAlgebraLength` computes restricted module length by local
lengths weighted with those residue degrees, using the existing native prime
filtration. These declarations extend `Module` and retain the Noetherian and
finite-length hypotheses of their respective conclusions.
