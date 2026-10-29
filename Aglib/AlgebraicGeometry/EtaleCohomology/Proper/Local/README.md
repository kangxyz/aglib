# Conditional local cohomology criteria

This family concerns the original map `cohomologyPullback i F q` for the
supplied morphism `i : S ⟶ X` and the original coefficient sheaves. It
assembles local comparison inputs; it does not establish general proper base
change.

## Presentations and original cohomology colimits

[Presentations](Presentations.lean) constructs an actual filtered presentation
in genuine `ZMod n` sheaves for a separated scheme and `n ≠ 0`. The original
coefficient is the point of both colimit cocones. Each stage is constructible,
finitely presentable as an underlying abelian sheaf, and finitely presentable
after restriction to every original affine open. The positive-modulus
condition is part of this producer.

[CohomologyColimits](CohomologyColimits.lean) proves preservation of these
original filtered colimits when `X` and `S` are qcqs, using the actual inverse
image and scalar-forgetting functors. Its comparison maps are the native
`colimit.post` maps. The source and target Ext universes remain independent;
the required indexing-shape colimits are explicit, with standard models
supplied at universe `u + 2`.

[AffineFPTransport](AffineFPTransport.lean) transports finite presentability
through the canonical isomorphism from a given affine-open inclusion to a
specified open immersion from a spectrum.

## The conditional criterion and its tests

[FiniteCogenerators](FiniteCogenerators.lean) defines the geometric
finite-constant-annihilator condition and factors a *given* finite-product
embedding through the actual annihilator of the original target. It does not
produce the finite embedding. [FiniteProducts](FiniteProducts.lean) identifies
the original cohomology product coordinates with the projection maps and
supplies finite annihilator tests while retaining the original finite family
and values.

[CogeneratorCriterion](CogeneratorCriterion.lean) reduces bijectivity to
explicit stage, colimit, and finite-annihilator inputs. In particular, its
`hfinite` remains an argument: for every constructible finite stage it requires
a nonempty `FiniteConstantProductEmbedding` of the original underlying
coefficient. It also requires source and pulled-back target cohomology-colimit
preservation, degree-zero injectivity `hzero` for finite constant annihilators,
and surjectivity `htest` for those annihilators in every degree. These test premises are not inferred from the existence of a presentation.

[ConstructibleComparison](ConstructibleComparison.lean) constructs the positive
presentation and colimit suppliers for separated qcqs `X`, qcqs `S`, and
`n ≠ 0`; it still takes `hfinite`, `hzero`, and `htest`. Its conclusion is
bijectivity of the original `cohomologyPullback`.

[ProjectiveLineCriterion](ProjectiveLineCriterion.lean) specializes the result
to the original closed-fibre pullback over a henselian local ring with
separably closed residue field. It still requires `n ≠ 0` and the explicit
geometric finite-embedding premise `hfinite` for every constructible finite
stage on the projective line. For a genuine coefficient it gives all-degree
bijectivity; the abelian specialization also retains the literal equation
`n • 𝟙 F = 0`. [ProjectiveLineCogenerators](ProjectiveLineCogenerators.lean)
supplies the finite-annihilator surjectivity and degree-zero injectivity tests
used in this specialization.

[CoefficientTransport](CoefficientTransport.lean) transports injectivity and
surjectivity of the same original pullback through an actual coefficient
isomorphism. The complete commuting-square argument is in
[Function/SquareTransport](../../../../Logic/Function/SquareTransport.lean).
Source and target Ext universes remain independent, and finite values are
resized through the actual additive `Shrink` isomorphism at the geometric tests.

## Review scope and provenance

The six-source local-criterion cut was reviewed as ACCEPT with its conditional
criterion boundary retained. Its input manifest SHA-256 is
`80288f3c3e4b3283b01f63322a5d296ee8e0f12467ec11c18a1e81ea14e6f1bd`. The
four-source local-assembly review records ordinary ACCEPT for its conditional
statements; its source-manifest SHA-256 is
`deab7f0c45bba8a020968fca5acc46d3ae240b9c2287d055e0a31becb833d864`, with
Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`. The exact promoted
source hashes and per-source correspondence are retained in the integration
packet manifest (SHA-256
`4bcd68942cb8b6cf1d759651462f437a320cf61cb6650640a5a2eceaa96d476a`). The
accepted scope leaves the global finite-embedding supplier and the general
assembly of proper base change open.
