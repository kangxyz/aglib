> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#site-cohomology-share-the-comparison-definition-not-only-its-proof) · [Context](original-context.md) · [Case index](README.md) · [Previous record](formal-line-bundle-algebraization-explicit-transports.md) · [Next record](étale-derived-comparisons-share-the-equation-then-specialize.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Site cohomology: share the comparison definition, not only its proof

These entries retain the delivering author's reported native build observations
from the adopted source packet, at the stated source versions. The packet
contains source identities and status records; its historical timings are not
measurements made by the present integration run.

The native derived-section comparison gives a second instance of the
[shared-constructor boundary above](nonflat-base-change-share-the-concrete-coefficient-constructor.md#nonflat-base-change-share-the-concrete-coefficient-constructor).
Generic coefficient-naturality lemmas compiled, but their concrete module-sheaf
specializations still exhausted 200,000 heartbeats at `whnf` or `isDefEq`.
Supplying explicit functors and universes, unfolding the concrete wrapper, and
using `simpa only ... using!` did not by themselves remove the expensive final
conversion. One diagnostic reported 77,412 reductions of `SheafOfModules.forget`
and 18,912 of each lifted-unit definition, but only 27 of `Functor.rightDerived`.
These are unfolding counts, not timings: they locate carrier conversion work,
not evidence that constructing the derived functor itself was the bottleneck.

The retained
[DerivedComparisonFactory](../../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedComparisonFactory.lean)
defines the **whole module-valued additive comparison** with its source object,
full functor and represented natural isomorphism as parameters. The generic
naturality lemma and the concrete terminal/scalar comparison definitions use
that same factory head. This avoids comparing independently elaborated
additive-equivalence chains after the native module carriers become concrete.
[DerivedGammaNaturality](../../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedGammaNaturality.lean)
then compiled in 8.43 seconds under the unchanged native guard. The source is
still native evaluation `rightDerived`, with actual `restrictScalars` where
required, and the same original Ext comparison; no new cohomology definition
or assumed comparison replaced it. This verifies the coefficient-naturality
fix, not every degree-zero, slice or boundary normalization using the factory.

The concrete degree-zero endpoint needed one further abstraction: the shared
factory and a generic H⁰ theorem still left a final carrier conversion, with
`DerivedTerminalZero` exhausting 200,000 heartbeats at `whnf`. In
[DerivedZeroPacket](../../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedZeroPacket.lean),
`moduleRepresentedPostcomp_ext_zero_of_eq` takes the **complete comparison `E`,
native unit value `y`, and original output class `z`** as parameters, together
with their equations identifying the canonical factory, unit and `Ext.mk₀`
class. It also retains the original section morphism and its equation under
the represented-section isomorphism. Rewrite these equations abstractly, so
the conclusion is literally `E y = z`, rather than reconstructing those
carriers during concrete specialization.
[DerivedTerminalZero](../../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedTerminalZero.lean)
then supplies the actual original comparison, section value and Ext class,
with `rfl` witnesses. The generic packet and concrete terminal/scalar H⁰ leaf
compiled in 5.58 and 8.42 seconds respectively, with stable source and clean
native guards. No concrete endpoint hypotheses, definitions, maps or budgets
were changed. This verifies these H⁰ endpoints, not the subsequent
`finalComparisonZero` consumer.
The same complete-`E`/`y`/`z` boundary, with canonical equality witnesses, also
made [DerivedScalarSlice](../../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedScalarSlice.lean)
compile in 78.57 seconds under a clean native guard, retaining the original
coefficient action and native chain restriction.

For the original module-to-abelian slice restriction square, abstracting only
the source map left another expensive conversion inside Ext: module restriction
followed by forgetting had to be compared with abelian restriction at the
coefficient object. The retained
[SliceNaturality](../../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/SliceNaturality.lean)
proves `extFullRestriction_square` over all four functors, including the actual
coefficient transport and its equation. It first proves
`toSheaf_overFunctorMap` at the sheaf-map level, then instantiates the complete
Ext equation. The leaf compiled in 87.68 seconds under the unchanged guard.
Carry both source and coefficient comparisons across the abstraction boundary;
do not leave their concrete object conversion for the final Ext rewrite.

A separate instance-synthesis failure required a different repair. Explicit
universes on the essentially-small-site Grothendieck theorem, and then on the
induced `HasSheafify` target, still left a constraint of the form
`u + 1 = max (u + 1) ?v` for `SmallModel`'s category. The retained
[Large/Injectives](../../Aglib/CategoryTheory/Sites/SheafCohomology/Large/Injectives.lean)
first binds the original `smallCategorySmallModel` at the precise
`SmallCategory.{max u v}` type, then synthesizes sheafification and applies the
native Grothendieck supplier. This generic leaf compiled in 4.13 seconds.
Pin the category structure before dependent synthesis when this exact
max-universe ambiguity occurs; annotating only the final theorem may be too
late. This is not evidence for globally changing instance priorities.

These measurements are successful native leaf builds, not controlled speedup
ratios. Reuse their existing receipts; documenting the repair does not require
another compilation or a downstream blanket rebuild.


