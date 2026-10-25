> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-the-completed-stalk-equation-through-specialization) · [Context](original-context.md) · [Case index](README.md) · [Previous record](retain-the-original-pullback-row-equation-boundary.md) · [Next record](specialize-the-whole-arc-argument-after-fixing-its-algebraic-data.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Keep the completed-stalk equation through specialization

The tensor and arbitrary-scheme completed-stalk comparisons in
[Spec/CompletionLocalRing](../../Aglib/AlgebraicGeometry/Spec/CompletionLocalRing.lean)
repeatedly reached the default recursion limit when a generic composite
of ring equivalences was applied to the actual stalks. Naming the
composite function alone did not close that boundary. Native run
`remote-540c701dce1447df9d7a70b82004351c` records recursion failures in both
the tensor and global specialization, alongside a separate affine-algebra
carrier error.

State the generic calculation and the concrete consumer through the SAME
regular `CompletionImageEq` definition, with the actual equivalence,
source/target completion maps, original stalk map and original element as
arguments. Its content is exactly `e (sourceMap s) = targetMap (originalMap s)`.
The `.eq` projection exposes that equality after an abstract equivalence
has been obtained. This retains the original map equation without asking
the specialization to normalize a newly expanded composite of stalk
isomorphisms, localization maps and completion equivalences.

For the affine chart, retain one raw ring carrier with its original
commutative-ring structure, and build the actual base algebra on that same
carrier. For the final point equation, retain the literal pullback and its
original projection, evaluate the proved chart-base equation by typed
`congrArg`, and compose explicit `Scheme.Hom.comp_apply` equations. Neither
step adds a flatness, normality, finite-type or completion-isomorphism
premise to the arbitrary-scheme completed-stalk comparison.

Source
`c8512946a69b5cad1b256cef8f274eae2f0a1edf293280ca38811abfbc39a894`
passed the full Spec module in 20 seconds in
`remote-0fb712b753214ed1bf3194b902d7a977`, source snapshot
`42b0e59dd8b032e4dc3b2ec827ff4f1eb84d81099ba7fa8756ef6aa0379d76df`.
The pinned toolchain and default budgets were unchanged. Coverage includes
the actual completed-stalk equation, residue-fibre correspondence and the
pointwise regularity comparison under the stated local finite-type
hypotheses. A subsequent proper global-regularity adapter is a different
source version and is not covered by this pass. Other modules failed in
the outer graph. No profiling or replay was used; these observations do
not establish a controlled speedup or a general compiler defect.

