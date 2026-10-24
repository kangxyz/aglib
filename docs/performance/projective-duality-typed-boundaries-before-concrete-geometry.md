> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#projective-duality-typed-boundaries-before-concrete-geometry) · [Context](original-context.md) · [Case index](README.md) · [Previous record](equation-proofs-presentations-and-structure-fields.md) · [Next record](nonflat-base-change-share-the-concrete-coefficient-constructor.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Projective duality: typed boundaries before concrete geometry

The 2026-10-18 projective-duality continuation supplies further successful local
cases under the pinned toolchain. These are compilation results, not controlled
whole-library speedup measurements. The original canonical maps and mathematical
hypotheses were retained.

**Paste whole natural transformations before taking components.** In
[Trace/Local](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Trace/Local.lean),
`traceLocalHomFactory_refine` proves the restriction equation over abstract
categories, functors and supplied natural isomorphisms. The geometric proof uses
the actual whole affine-model comparison and only then takes its component.
This avoids repeatedly comparing expanded presentations at `Spec`. The maintained
Local, Gluing and original Core construction compiled successfully. It does not
by itself discharge every later residue or unit conversion. The newer
[affine descent transport](../../Aglib/AlgebraicGeometry/Descent/Modules/Fppf/CompTransCoherence.lean)
uses the related method of identifying individual leaves by equations or `HEq`
inside one generic transport proof. Its final application passes `rfl` and
`HEq.rfl`; it does not ask the kernel to compare two large concrete composites.

**Separate the source, derived core and coefficient factors.** The canonical
[principal](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/ModelCharts/Principal.lean)
and [ambient](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/ModelCharts/Ambient.lean)
chart equations now use typed intermediate squares before the final paste.
For the ambient coefficient factor, normalize the native quotient-ring
presentation in the supplied equation and in the target separately, then paste
the resulting equation. A large final `rfl` or indiscriminate unfolding had left
that representation change implicit. Both maintained modules compiled. Their
private `principalWholeChartPaste` and `ambientWholeChartPaste` retain documented
400000-heartbeat allowances after measured 200000 failures; the public consumers
and other helpers use the default budget. Those finite allowances are part of
the measured boundary, not evidence that increasing a budget alone solved the
conversion problem.

**Transport dependent degrees before instantiating the geometry.** In
[Smooth/Trace](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Smooth/Trace.lean),
the direct all-degree proof failed even with a provisional 1,000,000-heartbeat
allowance. The retained proof first establishes
`purity_transport_eq_single_trace` for abstract abelian categories, objects,
functors and the original comparison family. It keeps the degree-zero input
literally at `0 + c`, instead of asking conversion to replace that index inside
reindexed morphisms. The private `singleReindexIso_output_inv_of_degree` adapter
eliminates an equality of the whole output-degree parameter before applying the
existing shift identity; it then specializes at `0 - d`. The actual geometric
formula and scalar-independence equation instantiate those typed facts.
Smooth.Trace and its final coherent consumer compiled with every declaration at
the default 200,000 heartbeats and recursion depth 1000. The original trace,
canonical isomorphism, all-degree statement and empty-source branch are unchanged;
no additional compatibility hypothesis or alternative derived model is introduced.
This is a successful proof-boundary change, not a controlled wall-time ratio.

**Use the original universal property before exposing a chosen preimage.** In
[Comparison/OpenTrace](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Comparison/OpenTrace.lean),
first prove the actual trace's top-homology equation, then lift that equation to
the installed bounded-below preimage. Attempting `change` directly through
`Functor.preimage` exposed its choice-based implementation. The retained proof
keeps that original preimage and trace; the complete open comparison and its
all-degree coherent consumer compiled.

**Check the representation and the failing phase before changing tactics.**
Explicit `CategoryTheory.Functor.comp_map` equations and pointwise isomorphism
cancellation closed the remaining coherent boundary wrappers. Fully qualify
`CategoryTheory.Functor.map_id` when a root `Functor.map_id` is also in scope:
the latter can be a different operation, rather than a slow categorical rewrite.
Inspect compact expression heads, implicit objects and selected instance names;
printing an entire derived-category expression can itself exhaust diagnostic
resources. A later successful declaration in a file with earlier errors is not
a successful module check.

Two fully expanded residue/unit corollaries remain unproved scratch candidates.
The published trace normalization uses the checked Core affine formula and the
original affine residue/unit laws; the final consumers already use those proved
interfaces. The failed conversion probes are not recorded as successful remedies,
and the expanded candidate declarations are not exported as proved theorems.

