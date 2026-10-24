# Native Hom-complex continuity

These leaves extend the existing `CochainComplex.HomComplex`, whose terms are
Mathlib's `HomComplex.Cochain`. They do not introduce another complex carrier.

- `Precomposition` constructs the original contravariant chain map and proves
  identity/composition equations. For a mono of source complexes and a
  termwise injective target, its degree maps are surjective. This is extension
  of arbitrary cochains, not an unsupported extension of cycles or chain maps.
- `Colimit` descends compatible cochains uniquely along the actual source
  colimit and proves strict compatibility with the differential.
- `Limit` uses this descent to construct an actual limiting cone over the full
  opposite source diagram. It works with independent object, Hom, and diagram
  universes, without a blanket exactness assertion for inverse limits.

For ordinal applications, restrict to all strict predecessors. The necessary
hypothesis in Stacks 0AAT is degreewise surjectivity to that entire predecessor
limit at every stage, not merely pairwise surjectivity. At a continuous limit
stage the actual source colimit supplies the Hom-complex comparison. At a
successor, termwise injectivity gives cochain extension. The independent
`CompatiblePrimitive` leaf supplies the local correction, but ordinal
compatible-primitive recursion and small-acyclic detection remain separate
proofs. The actual inverse-limit acyclicity theorem is not asserted here.

Compiler acceptance is tracked per leaf by the coordinating owner. Pending
source interfaces are not a claim of global K-injective replacement existence.

The coordinating compiler accepted `CompatiblePrimitive` in graph 033,
`Precomposition` in 034, `Colimit` in 038, `Limit` in 042, and the full
`Continuity` consumer closure in 045. Accepted source bytes are preserved;
this compilation evidence is distinct from final audit evidence.

`Continuity` is the actual full-limit comparison consumer: for a monomorphism
from the colimit of the whole earlier source diagram into a source stage,
precomposition onto the entire native inverse Hom limit is degreewise
surjective. In an ordinal filtration, the diagram must contain every strict
predecessor. The ordinal acyclicity proof cannot substitute pairwise
transition epimorphisms for this statement.

`ShiftDetection` uses the existing native homology/cohomology-class comparison
and original shift adjunction to derive all-degree Hom-complex acyclicity
from nullhomotopies on every source shift. It does not replace that hypothesis
by degree-zero vanishing or assert the global small-test detection theorem.

The subsequent `EvaluatedLimit` / `WellFounded` source wave closes the universe
interface without identifying source-index and morphism universes. The former
constructs particular evaluated Hom-complex limits directly from cochain
descent. The latter uses the original source predecessor colimit comparison,
not a pairwise transition, to feed the well-founded compatible-primitive
inverse-limit theorem. These new leaves are pending compiler acceptance; the
045 acceptance above concerns only the earlier continuity closure.

`ShortExact` proves that the original reversed precomposition maps of a
short exact source sequence are short exact for a termwise-injective target.
Degreewise cokernel descent proves the kernel/image equality. This supplies
the successor step for acyclic source filtrations and does not assume that
arbitrary cycles extend through a monomorphism.

`SourceIso` transports the native Hom complex along an actual source
isomorphism by the original precomposition maps. `EvaluatedLimit` constructs
the particular degreewise limits supplied by source colimits, without
assuming all diagrams of that size have limits in the abelian-group value
universe. `WellFounded` combines these comparisons with the independent
inverse-limit acyclicity theorem for the original full predecessor diagrams.
These suppliers do not by themselves construct a global replacement functor.

The actual `EvaluatedLimit` was accepted in graph 066 and `WellFounded` in graph
074. The generalized inverse-limit acyclicity closure was accepted in 070. Thus
the original full-predecessor source comparison now has a compiled native
consumer, with independent universes and no arbitrary-shape limit premise.
