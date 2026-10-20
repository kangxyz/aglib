# Signed product sequences

[ProductSequence](ProductSequence.lean) defines
`CategoryTheory.ShortComplex.productSequence` in any abelian category from a
commuting square. Its first arrow is the ordered product lift and its second
arrow is the signed difference. Invertibility of either opposite pair gives
an explicit splitting and short exactness. An additive finite-limit-preserving
functor transports the same sequence through its native product comparison.

The first native consumer is vanishing of actual scheme-module cohomology for
binary products. This is generic homological algebra; no field or scheme
hypotheses occur in this leaf. The extraction preserves Quillen source names,
so downstream Quillen must replace its historical implementation by an import
of this canonical leaf before importing both libraries together.
