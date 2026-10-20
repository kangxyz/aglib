# A specified spectral completion and its actual Galois action

`Witness.lean` defines `AlgebraicClosure.DenseEmbeddingExtends f`: there is an
actual ring homomorphism from `AlgebraicClosure F`, extending the given base
map `f`, with dense range. This predicate contains no completeness,
algebraic-closedness, norm-compatibility, or isometry field. Any such properties
of a target are separate supplied assumptions or separately proved results.

The parent `CompletedAlgebraicClosure.lean` uses Mathlib's spectral norm on the
original `AlgebraicClosure F` and literally
`UniformSpace.Completion (AlgebraicClosure F)`. Its namespace is
`AlgebraicClosure.SpectralCompletion`. The embedding is the composite of the
actual base-field and completion maps, with its exact extension and density
equations. The complete nontrivially normed ultrametric characteristic-zero
base field supplies the completion's algebraic closedness through Mathlib's
dense-subfield theorem. The small-unit existence theorem constructs this
particular completion and its properties; it is not a producer of an arbitrary
prescribed target's dense-embedding predicate.

`Galois.lean` constructs isometric completion automorphisms from the original
algebraic automorphisms, proves the composition law and embedding equations,
and extends automorphisms of the literal relative algebraic closure through
its specified image equivalence. `AlgebraicUnits.lean` alone imports the
[cyclic-unit carrier](../../../../FieldTheory/Units/CyclicQuotientDescent.lean)
for its final action formula. The generic completion and automorphism leaves
have no unit-quotient or curve dependency.
