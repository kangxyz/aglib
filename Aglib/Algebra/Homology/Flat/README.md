# Universal tensor exactness and native flat cycle models

Import `Aglib.Algebra.Homology.Flat.UniversalTensor` for the lower terminal-cycle
criterion. The coefficient ring `R : Type u` is commutative; the native module
objects may live in independent universe `v`. The original tensor test modules
may remain in `Type u`, as in the native tensor-injectivity flatness criterion.

For an actual `ShortComplex (ModuleCat.{v} R)`, middle exactness after tensoring
with a test module makes the tensor of `S.fromOpcycles` injective. The original
`S.pOpcycles` is surjective and remains so after tensoring; its two original
factorization equations give the proof. If this middle tensor exactness holds
for every test module and `S.X₃` is flat, the actual native `S.opcycles` is flat.
Flatness of `S.X₂` then makes the actual image of `S.f` flat, and flatness of
`S.X₁` makes the actual kernel of `S.f` flat. The proof uses the original
cokernel and range-restriction maps, and the lower native flat-kernel lemma.

`CochainComplex.flat_cycles_of_universally_lTensor_exact K b` concludes that
the actual cycle object `K.cycles b` is flat when the original terms at
`b`, `b + 1`, `b + 2` are flat and the original two differentials are exact
after every module tensor product. No boundedness, finite generation,
projectivity, purity property, or independently supplied terminal-cycle
flatness is assumed. An unbounded exact tail of flat terms does not supply the
universal tensor-exactness hypothesis.

The current consumer is the original good truncation of the structural-ring
Cech complex. Geometric universal tensor acyclicity must come from actual
all-ring base change and the sharp finite affine-cover bound; coefficient
relative flatness supplies the original section-term flatness. The algebraic
criterion itself does not assert this geometric input or cohomology finiteness.

Import `Aglib.Algebra.Homology.Flat.Truncation` for
`CochainComplex.flat_truncLE_X_of_universally_lTensor_exact`. When all original
terms are flat and the same next-degree universal tensor exactness holds, every
term of the native `K.truncLE b` is flat. Interior terms use the original
native term isomorphisms, the boundary uses the proved actual flat cycle module,
and terms above the bound are zero. Native strict bounds and the original
`K.ιTruncLE b` remain unchanged; its existing quasi-isomorphism criterion retains
the actual cohomological upper bound `K.IsLE b`.

The UniversalTensor leaf was compiled alone through the shared serialized
wrapper, receipt `1792087312589474000-32451`.
The Truncation leaf passed separately, receipt `1792087504423936000-36098`.
The external `work/proper-validation/UniversalTensorConsumer.lean` checks the
native opcycles, kernel and actual cycle conclusions in independent scalar and
module universes; it passed with receipt `1792087411322961000-34768`. The
inspected proofs use only `propext`, `Classical.choice` and `Quot.sound`.
The same probe was extended to every native good-truncation term, including
the actual boundary cycles; the refreshed successful receipt is
`1792087856848642000-41732`, with the same standard axioms.

Import `Aglib.Algebra.Homology.Flat.Kernel` for preservation of the original
boundary kernel under arbitrary scalar extension. Universal middle tensor
exactness and flatness of `S.X₂`, `S.X₃` prove that tensoring the original
kernel inclusion gives an injective exact kernel pair. The source `S.X₁`
and the new coefficient ring need not be flat. This proves the native
`PreservesLimit (parallelPair S.f 0)` property for `extendScalars σ`.

`Aglib.Algebra.Homology.Flat.ScalarExtension` applies this proved preservation
to the canonical comparison from `CochainComplex.MapTruncation`.
`extendScalarsTruncLEIso σ K b h` identifies extension of the original good
truncation with good truncation of the original extended complex. Its
inclusion equation retains the literal mapped `K.ιTruncLE b`, and its
naturality equation retains the original coefficient maps. Only terms
`b + 1`, `b + 2` must be flat for this comparison; flatness of the boundary
term is needed separately when asserting flatness of every truncation term.
The original mapped inclusion is a quasi-isomorphism when the actual
extended complex is cohomologically bounded above by `b`. The ring map is
unrestricted, and scalar, coefficient-ring and module universes are independent.

The Kernel and ScalarExtension leaves passed separately with receipts
`1792089499702359000-72346` and `1792089718880498000-78426`.
The external `work/proper-validation/ScalarExtensionTruncationConsumer.lean`
checks the kernel-preservation interface, canonical isomorphism, original
inclusion, coefficient naturality and actual quasi-isomorphism in independent
universes. It passed with receipt `1792089997869538000-84801`; the inspected
proofs use only `propext`, `Classical.choice` and `Quot.sound`.

## Bounded-above flat complexes and arbitrary scalar extension

[BoundedAcyclic](BoundedAcyclic.lean) uses an actual strict upper term bound.
`CochainComplex.flat_cycles_of_exact_above K b n h` proves that the original
`K.cycles n` is flat when every term is flat, `K` is strictly at most `b`,
and the original complex is exact strictly above `n`. Descending induction
uses the original short exact cycle sequences and the lower flat-kernel
theorem. In contrast with the unbounded Cech tail, this strict upper term
bound supplies a starting zero cycle module for the descent.
`flat_truncLE_X_of_exact_above` consequently proves flatness of every term
of the unchanged native good truncation at `n`.

For an actually acyclic complex with these flat terms and strict upper bound,
`universally_lTensor_exact_of_acyclic` proves that the literal original
differential pair remains exact after tensoring with every module, in an
independent test universe. `acyclic_extendScalars_of_flat` proves actual
acyclicity after every ring homomorphism. Neither statement assumes a lower
term bound, a Noetherian ring, or flatness of the test module or ring map.

`flat_X_mappingCone` proves term flatness of the original signed cone by its
native biproduct comparison. `quasiIso_extendScalars_of_flat` then proves
that the literal native scalar-extension map of a quasi-isomorphism between
two bounded-above flat complexes remains a quasi-isomorphism after every
ring homomorphism. The two strict upper bounds may differ. The proof applies
the preceding actual acyclicity theorem to the original cone and uses the
native additive scalar-extension cone isomorphism. It introduces no family
of assumed base-change quasi-isomorphisms.

The BoundedAcyclic leaf passed with receipt `1792097473649095000-35206`.
Its external `work/proper-validation/BoundedFlatConsumer.lean` passed with
receipt `1792097532858517000-36152`, checking actual cycles and truncation,
literal tensor differentials, all-ring acyclicity, and the original mapped
quasi-isomorphism in four independent universes. All five inspected
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Arbitrary module tensor on the same complexes

[ModuleTensor](ModuleTensor.lean) uses native `tensorLeft J` and `tensorRight J`
in `ModuleCat R`, with the ring and module carriers in the native common
universe. `acyclic_tensorLeft_of_flat` and `acyclic_tensorRight_of_flat`
retain an actual strict upper term bound and original term flatness.
`quasiIso_tensorRight_of_flat` tensors the literal original map of two
bounded-above flat complexes. Its proof applies
`universally_lTensor_exact_of_acyclic` to the actual bounded flat mapping
cone and uses the native additive mapped-cone comparison. The coefficient
`J` is arbitrary; it need not be flat, finite, projective, or injective.

The two `ShortComplex.tensorLeft/Right_preservesKernel_of_universally_lTensor_exact`
results prove only the displayed boundary-kernel preservation, from the
original universal tensor exactness and flatness of the following two terms.
`CochainComplex.tensorRightTruncLEIso` is the existing native good-truncation
comparison with that exact kernel hypothesis discharged. Its
`_hom_ιTruncLE` equation preserves the actual mapped original inclusion.
No tensor functor is given a global preservation-of-homology instance.
The bounded flat projective twist Cech model is a current consumer.
