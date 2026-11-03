# Algebraic categories and homology

[ModuleCat](Category/ModuleCat/README.md) supplies scalar restriction, localization, quotient-ring actions and canonical adjunction units on arbitrary modules. [FGModuleCat](Category/FGModuleCat/README.md) owns the actual finitely generated module category. Its abelian/exact structure uses Noetherianity; the objects and several scalar constructions are defined more generally.

[Homology](Homology/README.md) supplies quasi-isomorphism detection by an actual acyclic cone. [TotalComplex](Homology/TotalComplex/README.md) proves that rowwise quasi-isomorphisms of first-quadrant module bicomplexes induce a quasi-isomorphism of the native total complex, over an arbitrary ring and with independent module universe. Generic injective/Ext comparison belongs to [CategoryTheory/Abelian/Injective](../CategoryTheory/Abelian/Injective/README.md).

[Graded coalgebra](Coalgebra/Graded/Primitive.lean) proves the native
degree-one dimension bound from the displayed grading, counit, coproduct and
vanishing hypotheses. It derives the needed degree-one primitivity from those
original maps; finite degree one and nontriviality remain explicit. No
Borel–Hopf splitting theorem is assumed.

[Tensor comparison](Coalgebra/Comparison.lean) constructs one coalgebra from
the displayed whole associativity and counit diagrams of a supplied tensor
comparison. [Graded tensor products](Graded/TensorProduct.lean) distribute
the original tensor of direct sums over exact degree fibres; their
[comparison](Graded/TensorProduct/Comparison.lean) and
[coherence](Graded/TensorProduct/Coherence.lean) laws keep the supplied maps,
degree transports and independent module universes. The
[graded external product](Graded/ExternalProduct.lean) uses the given graded
families and original Koszul-signed tensor. Its
[source identity](Graded/ExternalProduct/SourceIdentity.lean) identifies the
same selected source with Mathlib's graded-tensor identification. The current
consumer is original structure-sheaf cohomology and its group coproduct.

The consumers are actual quasicoherent/coherent sheaf functors and the scheme-cohomology comparison chain. Module paths use `Aglib.Algebra`; declaration owners include `ModuleCat`, `CochainComplex`, `HomologicalComplex₂` and `ComplexShape`.

[Polynomial/Laurent coefficient diagrams](Polynomial/Laurent/README.md) provide the actual scalar maps used by relative affine-space and coefficient base change. Generic [site module tensors](Category/ModuleCat/Sheaf/Tensor/README.md) lie below scheme-specialized tensor and projection-formula constructions.

[Automorphisms](Module/Automorphism/README.md) and
[commuting automorphisms](Module/CommutingAutomorphisms/README.md) use actual finite
projective modules, tensor scalar extension and the ordered Laurent action.
Their support and specialization formulas retain the displayed flatness,
Noetherian, domain and regularity hypotheses. Natural or integer coefficients
obtained from `Module.length` retain the separate finiteness requirement for
casting back from `ENat.toNat`.

[NormalizedQuotient](Group/NormalizedQuotient.lean) uses the supplied additive
retraction and subgroup; [Torsion](Group/Torsion.lean) transports actual torsion.
[Finite product projections](Ring/Pi/README.md) and
[QuadraticNorm](QuadraticNorm.lean) provide lower algebraic interfaces.

[DirectSumTransport](DirectSumTransport.lean) identifies a computed direct-sum
linear equivalence from its summand equations and proves the specified
canonical map bijective. The constructor and its theorems share the same
regular definition. Its module universes are
independent, allowing comparison with larger-universe original cohomology.

[Injective dual](Module/Injective/Dual.lean) proves exactness of native dual
maps over a self-injective commutative ring. For nonzero `n`,
[ZMod injectivity](Module/ZMod/Injective.lean), [dual](Module/ZMod/Dual.lean),
[finite dual](Module/ZMod/FiniteDual.lean) and [perfect pairing](Module/ZMod/PerfectPairing.lean)
supply exact dualization, finite biduality and native `IsPerfPair` criteria.
Modulus zero is excluded from self-injectivity.

[ZMod endomorphisms](Category/Grp/ZModEndomorphisms.lean) parametrize the
actual additive endomorphisms of the lifted cyclic group by scalars for
positive modulus, including one. [CyclicPairing](Module/ZMod/CyclicPairing.lean)
gives a native perfect-pairing criterion from an actual scalar generator and
bijective evaluation, and handles subsingleton modules.
