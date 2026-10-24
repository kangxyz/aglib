# Conversion boundaries

Return to the [performance lookup](../PERFORMANCE.md).
These methods concern an identified conversion, inference or rewriting boundary.
A timeout message alone does not identify its cause.

## Type the complete boundary

Use the actual source and target objects, Hom carrier, intermediate isomorphism,
values and relevant structures. Keep one representation throughout the proof:
for example, bind `M : X.Modules` before using `M.presheaf.map`, rather than
switching between its sheaf and module-sheaf presentations at the final step.
Type both endpoints of a transport and the lambda passed to `congrArg`.

In the module-section nonvanishing case, the retained proof changed to the
actual presheaf maps and applied their composition law. The repaired complete
module passed in 11.14 seconds at the ordinary budget. Other proof repairs and
cache conditions differed, so this shows removal of that failure, not a measured
speedup attributable to one annotation.
[Original case and source identity](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-one-representation-of-module-sections).

The Godement Tensor comparison aligned the inferred object `F.obj (G.obj C)`
with its composite-functor presentation. A matched isolated module comparison
was reported at 144.58 versus 103.82 seconds. A later artifact-producing run
reported 60.66 seconds under different output/profiling settings, so it does
not extend that matched ratio. Early wrapper observations did not certify
actual frontend flag propagation; later resource-fit evidence has its own basis.
[Tensor, Span and wrapper conditions](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#what-the-measurements-establish),
[follow-up observations](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#recorded-follow-up-measurements).

An annotation that elaborates to the same core term need not help. An actual
structure or mathematical mismatch still needs its original comparison proved.

## Compare whole equations before evaluating components

Compose or normalize the relevant original natural transformations,
isomorphisms and adjunction equations over variable objects, then evaluate once.
Keep the consumer's exact association and whiskering convention.

The exceptional-image integration supplies two examples: `ModuleSourceExchange`
retained a whole original isomorphism comparison before its component;
`ModuleCartesianExchangeMate` transported equality of the whole Cartesian
comparisons before obtaining the original mate equation by transitivity.
Their recorded producers passed in 42 and 13 seconds. An opaque arrow chase
alone had not removed the latter failure.
[Original observations](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#whole-module-exchange-comparisons-before-evaluating-components).

This does not prescribe the largest possible abstraction. The
[affine-refinement case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#affine-refinement-through-literal-mate-types)
instead improved the representation by removing a Type-valued data constructor
and retaining literal component arrows. Choose the smallest complete boundary
that preserves the needed original interface.

## Carry complete values and canonical equations

If a generic proof still becomes expensive when specialized, give it the actual
comparison, input/output values and source/target transports as typed parameters.
Its conclusion should already have the consumer's original equation, such as
`E x = y`. Supply the actual values and their proved canonical equations once.

The [site-cohomology cases](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#site-cohomology-share-the-comparison-definition-not-only-its-proof)
show why abstracting only the map, the last scalar calculation or an intermediate
component constructor was insufficient. Some needed the complete module-valued
comparison factory as well; see [shared constructions](shared-constructions.md).
A generic theorem passing does not establish that its concrete consumer passes.
An equation supplied as a parameter must still be proved for the original data.

## Fix dependent transports before concrete specialization

Keep degree equations, finite-subtype ranges, Over source objects and chart
index families explicit before forming dependent carriers. Preserve the actual
arithmetic expression and equality orientation used by the provider.
A `subst` selecting another equality, or simplification of an already concrete
carrier, can measure a different conversion.

The [formal line-bundle cases](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#formal-line-bundle-algebraization-explicit-transports)
and [tuple-cochain cases](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#original-tuple-cochains-normalize-typed-carriers-before-transport)
retain original transport equations. Where relative objects have differently
presented structural maps, use the original comparison arrows and triangles;
do not force an equality-rebase that replaces the coefficient structure.

## Isolate finite witness selection

Typing equivalence endpoints alone may leave expensive preimage selection.
In the finite Ext test, componentwise preimages still exhausted the ordinary
budget after the actual source and target additive equivalences were typed.
The repair proved `surjective_of_pi_transport` over plain functions, the two
actual equivalences and their literal component equation, then supplied the
original Ext comparison and coefficient-naturality law.

The repaired full leaf passed in 7.7 seconds. It retained arbitrary finite-index
universes, independent Ext sizes and the original preadditive/additive conditions;
no new premise or budget was supplied.
[Original witness-selection case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#finite-ext-tests-isolate-witness-selection).

## Use finite typed calculations for an identified rewrite failure

Apply the original map's theorem directly when it already has the needed type.
Compose exact equations with typed `congrArg`, `congrArg₂` or `Eq.trans`
when a broad rewrite exposes the wrong carrier. Stop extensionality at the
intended element or transformation level. Qualify colliding names such as
`CategoryTheory.Functor.map_id` and `Limits.Pi.map`.

Keep these different failures distinct:

| Recorded failure | Retained local repair |
| --- | --- |
| Permutation ordering during `simpa only [mul_comm]` | Compose `(mul_comm w z).trans hzw` directly. [Case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#binary-form-section-and-geometric-point-typing). |
| Forward and reverse composition rules form a rewrite loop | Use a finite calculation through the original unit, instead of both simplification directions. [Case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#use-a-finite-original-unit-calculation-for-constant-direct-image-coordinates). |
| `p = C (p.coeff 0)` rewrites the occurrence of `p` inside its own right side | Use that equality once through congruence and composition. The repaired lower module passed in 7.6 seconds; later extensions have separate coverage. [Case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#avoid-self-referential-coefficient-simplification). |

These are targeted remedies, not a general ban on `simp` or `rw`.

## Prefer an available native mathematical interface

Use the original map with `Ideal.map_pow`, the native sheaf property before
concrete unit evaluation, or a proved full-preimage equation before transporting
through `Functor.preimage`. Replacing a native representative interface with
unfolded evaluation-inverse seeds can recreate the expensive boundary.

The [terminal coefficient-chart repair](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#rebase-sections-to-the-terminal-coefficient-chart-before-equality-descent)
uses a simpler route only after the original fixed-base natural isomorphism was
available. Its mathematical precondition matters; it is not a universal
performance trick. The recorded result retains its affine-stage and small-index
hypotheses and original section maps; it does not claim full scheme-limit
continuity.

The linked fixed records contain full source and observation details. Their
then-pending consumers describe those runs, not a current mathematical backlog.
