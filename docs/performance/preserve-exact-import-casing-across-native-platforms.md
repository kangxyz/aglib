> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#preserve-exact-import-casing-across-native-platforms) · [Context](original-context.md) · [Case index](README.md) · [Previous record](picard-tangent-space-prove-additive-group-algebra-abstractly-then-specialize.md) · [Next record](separate-the-structural-h0-interface-from-its-h1-consumer.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Preserve exact import casing across native platforms

Use the basename returned by the pinned source tree when adding an import.
A macOS filesystem may accept reading `ModuleCat/ULift.lean` while the actual
Mathlib file is `ModuleCat/Ulift.lean`; the Linux compiler then rejects
`Mathlib.Algebra.Category.ModuleCat.ULift` before elaborating the module.
The canonical import is `Mathlib.Algebra.Category.ModuleCat.Ulift`.

At Mathlib `d13f23b7`, the casing-only repair of `FiniteComplexModel` from
`512d57bc` to `d5922ea6` passed in native `bf37d261` (5.9s). The same wrong
import later blocked the new derived Hom-cohomology bridge in `0eaa2726`.
Resolve this known failure with `rg --files` in the pinned owning directory;
reading a guessed path locally does not establish its exact casing. This
uses existing compiler feedback and requires no separate build or audit.

