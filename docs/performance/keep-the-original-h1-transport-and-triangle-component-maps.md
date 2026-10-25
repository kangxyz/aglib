> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-the-original-h1-transport-and-triangle-component-maps) · [Context](original-context.md) · [Case index](README.md) · [Previous record](retain-the-given-grading-in-an-exceptional-chart-quotient.md) · [Next record](local-instance-names-must-remain-distinct-across-actual-imports.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Keep the original H1 transport and triangle-component maps

The original-map comparison in
[DerivedStructure](../../Aglib/AlgebraicGeometry/Cohomology/Proper/DerivedStructure.lean)
first reached a maximum-recursion-depth failure in `remote-38af34a7` while
changing a concrete composite of homology, module and linear-equivalence
maps. Its maps include the actual derived structure unit and the original
cohomology map. Expanding those constructions together is unnecessary.

The retained repair proves `originalLinearTransport_comparison` over variable
modules, linear equivalences, an isomorphism and the original morphisms.
The concrete consumer supplies its two definitions by reflexivity and the
original functor-composition equation. Thus the comparison is transported
after fixing the module carriers, rather than by unfolding the concrete
derived geometry during a final `change`.

Two triangle-component proofs had a separate representation issue. A closing
`simpa` split the original `RF.map (single phi ≫ unit)` only in its input,
leaving the expected component in the original unsplit form. Native
`remote-bd14382` reports those exact two mismatches. Compose the already
passed single-unit and comparison-triangle component equations directly,
using `congrArg`, and retain the raw mapped composite throughout. These are
the same original maps; no replacement naturality or compatibility premise
is added.

The complete Main source `fc21a757` passed native compilation in
`remote-3326d6a6` (313 seconds), followed by its actual general first-H1
injection consumer `8aaddba7` (6.3 seconds). Standard heartbeat, synthesis
and recursion limits were retained. This establishes successful completion
of the module on the repaired representations; the duration is not a
controlled speedup measurement. Keep this passed source and its compiled
outputs while repairing independent upper consumers.

