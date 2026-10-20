# Finite correspondences on the two-dimensional torus

The namespace `AlgebraicGeometry.Torus.FiniteCorrespondence` uses the actual
Laurent algebra `MonoidAlgebra R (Multiplicative (ℤ × ℤ))`, with its original
ordered coordinates. Its labels are the shared lower carrier
`MonoidAlgebra.FiniteDominantPrime R`: prime quotients that are finite over
`R` and whose prime contracts to zero. No second two-torus label type is
introduced here.

`Basic` realizes every label as an integral closed subscheme of the affine
torus, finite and dominant over the base. `Subscheme` gives the independent
ideal-sheaf presentation and its defining-ideal dictionary. The reverse
prime/subscheme equivalence requires a reduced base. `FibreSections` identifies
the literal scheme-theoretic fibre and its localized quotient length;
nonreduced fibres are retained.

`ModuleCycle` takes local lengths of the original module with two commuting
automorphisms. Noetherianity supplies finite support and finite lengths before
their natural and integer interpretations. `PointModule`, `FieldPullback` and
`ScalarPoint` construct the field point objects, field-extension cycle map and
rank-one scalar cycles. Point objects are constructed over fields; arbitrary
finite dominant prime quotients are not assumed projective or flat.

`DominantFibres`, `FibreLength` and `FlatPullback` handle flat scalar extension
using the actual coefficient algebra maps. `PrincipalFibres` defines the
quotient-fibre cycle map from literal localized quotient lengths.
`PrincipalDominance`, `PrincipalComposition` and `PrincipalInterchange` prove
closure, composition and principal squares with their explicit surjectivity,
principal-kernel, normal-domain, surviving-coordinate and Noetherian hypotheses.
The first specialized prime quotient may have scalar torsion; regularity is
proved on its required minimal factors. `FlatDictionary`,
`FlatPrincipalComposition` and `CoefficientComposition` retain the corresponding
mixed flat/principal identities and explicit ring maps.

The generic length lemma extracted from `FibreLength` belongs to
`Aglib.RingTheory.Localization.MinimalQuotientLength`, namespace `Module`.
It requires a Noetherian quotient ring and does not require the ambient ring
to be Noetherian. All length comparisons use extended-natural lengths;
finite-length premises are retained before conversion to natural numbers.

`SimplexFaces`, `ModulePrincipalNaturality` and `SimplexFaceIdentities` apply
the actual simplex face maps in every degree, with the original variance and
indexed identities. `SimplexFieldPullback` and `SimplexFunctoriality` handle
field-coefficient maps in every degree. `LowSimplexFaces` and
`SimplexFieldFaces` cover the five low face cases, indexed by `j : Fin 2`.
The statements introduce no characteristic restriction. `ScalarTransport`
uses the existing `AlgebraicSimplex.CoefficientEquiv` for coefficient
isomorphisms, and proves their actual quotient, prime and cycle transport.

`ScalarGraphCycle`, namespace `ScalarGraph`, separately retains the literal
one-variable Laurent prime labels and sends them to the two-variable labels
along the scalar graph. Tensoring on the right by a scalar unit pushes the
original one-torus cycle along `x ↦ (x, f)`, with no sign or degree factor.

These are affine scheme, module and local-length theorems. No Picard or
Hilbert representability, purity theorem, or identification with an external
motivic composition law is asserted. The source is the 26-file torus family
at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`; individual leaves
record their source file and SHA-256 hash. The seven coefficient-equivalence
prefix declarations of `ScalarTransport` are reused from the native simplex
family, and the common prime-carrier torsion-freeness theorem is reused from
the native monoid-algebra family.
