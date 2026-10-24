> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#original-tuple-cochains-normalize-typed-carriers-before-transport) · [Context](original-context.md) · [Case index](README.md) · [Previous record](cohomology-cone-legs-specify-the-actual-scheme-endpoints.md) · [Next record](reindexed-direct-image-comparisons-evaluate-a-whole-identity-first.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Original tuple cochains: normalize typed carriers before transport

With Lean 4.34.1 and Mathlib d13f23b, graphs 142–151 of the continuity task
encountered implicit-transparency endpoint mismatches and 200000-heartbeat
`whnf` failures while rewriting native Hom-complex carriers and tuple-product
generators. Unannotated product vertices also forced unnecessary reduction of
chosen limit cones. No mathematical product-preservation assumption was missing.

Construct the degree maps first on the explicitly typed original Hom groups.
Use named original product objects, tuple generators and site arrows, and
transport the native chain-map and tuple-projection equalities by whole-value
`congrArg`. Evaluate the free-family Yoneda comparison through those typed
generators rather than unfolding the complete Hom complex during rewriting.
For dependent products of section equivalences, first map the actual abelian
isomorphism through `forget`, then use the native type isomorphism equivalence.

Graph 148 accepted `Continuity.TupleBaseChange` in 4.3 seconds; graph 152 accepted
generic `Continuity.FamilyBaseChange` in 5.1 seconds and its actual etale adapter
in 3.4 seconds. These are full-leaf native acceptance results, not benchmarks.
No budgets were raised and no extra tests, audits or kernel replay were run.
Only the additive Hom cochain comparison is proved invertible; the underlying
map of free tuple presheaves is not asserted to be an isomorphism.

The corresponding `Stalk/PullbackLimitCoefficient.lean` encountered the same
concrete-component expansion in its naturality proof (graph 146). Its accepted
repair also specializes a whole original triangle transformation before a single
coefficient evaluation. Explicit native endpoint isomorphisms avoid relying on
simp to identify constant-functor objects with the original sheaf objects. The
constant-diagram colimit insertion equation is proved in an abstract category,
with independent index and target object/morphism universes, then instantiated
without unfolding the concrete sheaf category. Proof helpers referenced by an
exposed definition must themselves be publicly accessible; merely putting the
construction in a tactic block does not remove that module visibility boundary.
The exact leaf passed graph 152 (67 s), with unchanged budgets and options. This
is acceptance evidence, not a benchmark or an additional validation cycle.

### Preserve native representative interfaces across geometric specialization

In the étale continuity implementation, a concrete matching proof repeatedly exceeded the
normal deterministic kernel budget even after its Scheme/Over geometry and abstract
functor algebra had been separated. The abstract helper consumed naked `P.map` values
and explicit evaluation-inverse seeds, whereas both the accepted input producer and
required conclusion used `etaleRepresentativeSection`. Specializing the helper therefore
forced simultaneous reduction of deep pullback-source objects, the original section
functor, and the evaluation-inverse endpoint types.

The successful repair keeps the native interface intact: prove equality transport for the
original coefficient sheaf and arbitrary Over objects, with
`etaleRepresentativeSection` on both sides and original coefficient sections as inputs.
Its proof uses the existing native restriction theorem. Specialize this theorem once to
the already-proved geometric arrows. Also align the geometric arrow's source and the
consumer statement with the literal native `Over.mk` source of `unitRepresentativeArrow`,
rather than requiring an additional source-object alias conversion under the section
functor. No replacement cohomology, extra mathematical assumption, increased budget,
or kernel replay is involved.

Normal compilation on 2026-10-23 accepted `BaseChangeUnitMatching` in 8.6 seconds and
its actual stage-sheaf amalgamation consumer in 2.5 seconds (graph157). These timings
validate this interface repair, not completion of the full scheme-limit continuity theorem.

