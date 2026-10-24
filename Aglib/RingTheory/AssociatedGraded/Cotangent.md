# The canonical cotangent map

For an arbitrary ideal `I` in a commutative ring `A`, this module constructs
the canonical coefficient action and symbol map on the actual associated
graded ring, defined by the original Rees quotient.

`associatedGradedCoefficientMap` gives the original action of `A/I` and
retains the coefficient equation on every scalar from `A`.
`cotangentSymbol` is the resulting `A/I`-linear map from the actual
cotangent quotient `I/I²`. It sends the class of an original `a : I` to
the original degree-one Rees symbol modulo the defining ideal.

`symmetricCotangentMap` extends this symbol map to
`Sym_(A/I)(I/I²)`. Its formula on every original ideal element is explicit.
`symmetricCotangentMap_surjective` proves that this map is onto: its image
contains the original degree-one Rees symbols, the retained degree-one
generation theorem gives every homogeneous component, and the original
graded decomposition gives every element of the associated graded ring.

No coefficient-field section, Noetherian hypothesis, chosen basis,
rationality, Gorensteinness or surjectivity premise is used. For a local
ring and its maximal ideal, the coefficient quotient is the original
residue field and the source is the symmetric algebra of the actual
cotangent space. The complete quadratic tangent-kernel theorem still
requires the genuine Hilbert-function and geometric suppliers. This
module does not assert a rational-double-point or resolution theorem.
