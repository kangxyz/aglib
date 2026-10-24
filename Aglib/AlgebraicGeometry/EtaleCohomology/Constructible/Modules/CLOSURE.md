# Finite-type module closure

This note concerns the existing `Modules.IsFiniteTypeLocallyConstant` and
`Modules.IsConstructible` predicates. Neither predicate is replaced. Local
values are `Module.Finite`, not finite sets; the coefficient-ring universe is
independent of the scheme and module-value universes.

## Local morphisms and generators

The lower `ModuleCat/Sheaf/FinitePresentationLifting` supplier proves local
surjectivity after applying `Hom(M, -)` to a locally bijective map when `M` is
finitely presented. It first lifts finitely many generators on a common
cover, then kills finitely many relations on a further common cover. The
actual quotient map supplies the resulting module morphism.

`ConstantLocalHom` applies this to the original constant-presheaf
sheafification unit. `ConstantRestriction` proves that a local unit equation
identifies the entire restricted original sheaf map with a constant module
map. These statements do not assume that the constant-sheaf functor is full
on disconnected charts.

The separate `FiniteGeneratorsLifting` supplier needs only local
surjectivity. It uses the finite span of actual lifted generators inside the
original section module. This preserves the original module-value universe,
even if the coefficient ring has a larger universe. `ConstantFiniteGenerators`
turns that section construction into a locally generating constant sheaf on
the actual slice. It does not claim that relations lift through an arbitrary
epimorphism or that extensions split locally.

## Closure strategy and native objects

`ClosureSums` constructs actual fibre-product charts for finite sums. The
zero, binary-product and finite-biproduct conclusions require no Noetherian
assumption. `ClosureConstant` identifies constant-map kernels and cokernels
with the original constant sheaves of their algebraic kernel and cokernel.
The kernel requires a Noetherian coefficient ring; the cokernel only requires
a finitely generated target. `ClosureLocality` composes actual etale covers
and their original inverse-image comparisons.

`EtaleRestriction` isolates actual etale restriction, its native inverse-image
comparison, and its original adjunction-unit equation. `ClosureCharts` uses
the original site equivalence and native `Equivalence.sheafCongr`; it does not
require limits over a larger site in the original module-value universe.

The higher local closure proofs use the actual arrow on a refinement of
trivializing charts. They do not replace the original sheaf morphism by a
purported global coefficient map. The categorical
`ShortComplex.ShortExact.exists_cokernel_presentation` supplier presents the
middle term using a locally lifted generating map, its actual kernel, and
the original short exact sequence. No projectivity or local splitting premise
is added.

These are weak-Serre closure statements: kernels and cokernels of morphisms
between coefficients in the class, and extensions with both endpoints in the
class. Arbitrary ambient subobjects need not be constructible, so no full
`ObjectProperty.IsSerreClass` instance is intended.

## Geometric dependency boundary

The upstream cut `ce36e3ddd906ec14e7116befa1680ae0c9e6c47e` supplies the
coefficient-independent `FiniteLocallyClosedPartition.intersection` and its
actual `Refinement` maps in `Constructible/FiniteColimits/Partitions`. Module
closure must consume these original partitions. Only transport of finite-type
local constancy through their original refinement maps is module-specific.
There is no competing partition or constructibility model in this family.
`ClosurePartitions` supplies this module-specific restriction transport and
the common-pair consumer. `ClosureConstructibleSums` consequently proves
affine-local constructible zero objects and finite sums without a Noetherian
hypothesis.

The positive-presentation and finite-stratification packet is distinct from
this local closure work. In particular, the packet's results for original
positive-modulus stages on separated schemes do not assert arbitrary
constructible ambient finite presentability or general nonseparated qcqs
stratification. Local module closure alone proves neither those assertions,
finite direct-image constructibility, cohomological finiteness, nor proper or
smooth base change.

## Validation status

The exact maximal `ClosureConstructible` graph was accepted by the native
build in batch 58 on baseline
`ce36e3ddd906ec14e7116befa1680ae0c9e6c47e`, with Lean 4.34.1 and pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Its accepted public interfaces include
finite sums over every commutative coefficient ring, and kernels, cokernels,
and extensions over Noetherian coefficient rings, for both the existing
finite-type locally constant and affine-local constructible predicates.

The proof chain includes the original finite-presentation local lifting,
constant-map restriction, finite-generator chart, categorical cokernel
presentation, and native geometric refinement suppliers. No proof placeholders,
new axioms, resource increases, replacement sites, or independent kernel replay
were used. This is acceptance of the exact closure graph, not a claim that
all broader cohomological or remaining geometric inputs are complete.
