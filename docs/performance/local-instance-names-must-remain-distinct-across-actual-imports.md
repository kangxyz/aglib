> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#local-instance-names-must-remain-distinct-across-actual-imports) · [Context](original-context.md) · [Case index](README.md) · [Previous record](keep-the-original-h1-transport-and-triangle-component-maps.md) · [Next record](limit-exposure-to-the-actual-public-implementation-boundary.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Local instance names must remain distinct across actual imports

A local instance still creates a declaration with a name. Incoming
`ClosedImmersion.RightAdjoint.FiniteSource.Derived` declared
`Scheme.Modules.instHasDerivedCategory_aglib`, which already belonged to
the existing `DirectImage.Restriction.Composition`. The isolated new provider
compiled as `f7fb6110`, but its actual NormalSurface consumer failed during
import in `remote-3326d6a6`, before any mathematical body was elaborated.

Rename the incoming local declaration to `finiteSourceDerivedCategory`,
keeping the identical `HasDerivedCategory.standard` value, universe and
priority. Preserve the existing library provider. Revised source `6870088d`
passed in `remote-f5e32cec` (17 seconds), and the same consumer then reached
its mathematical body. This verifies the import repair; it is not a pass
for that still-pending consumer. Use distinct or appropriately private names
for local declarations in new files rather than relying on local instance
visibility to isolate their declaration names.


