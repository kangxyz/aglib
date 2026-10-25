> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#augmented-amitsur-differentials-and-typed-tensor-coordinates) · [Context](original-context.md) · [Case index](README.md) · [Previous record](shared-full-preimage-witnesses-for-action-descent.md) · [Next record](evaluate-original-geometric-stalk-units-through-typed-projections.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Augmented Amitsur differentials and typed tensor coordinates

At Lean 4.34.1 and the pinned Mathlib revision, specializing
`CochainComplex.of_d` at the augmentation degree failed to elaborate the literal
degree-one codomain in [Augmented](../../Aglib/Algebra/Homology/Amitsur/Augmented.lean).
The diagnostic exposed different presentations of native `Nat` addition and
one projections. The retained proof first establishes the zero composite with
the actual alternating coface differential. It unfolds only
`CochainComplex.of.d`, splits its condition, and rewrites the zero composite
before the native `eqToHom` transport. The original complex and augmentation
are preserved. Broad simplification and a private import-all attempt were not
adopted.

Failed run `remote-772d892e9490429d84615f3e48a07a79` has source digest
`aa1eb091b74dea36b446b2e3792c7145dc9deb709067687b00729ff5bd54232e`.
The repaired provider passed in 2.7 seconds in
`remote-2e30c4f1fceb4bce836fd0353fc61b09`, source
`c8d8bb40c1ea4f15363248b8b372c68971e76e6fd3a8028f7345e1e8caee333b`.
Separate downstream failures in that invocation are outside this success claim.

The scalar extra-degeneracy equations also failed when rewriting partially
unfolded native wide-pushout and tensor objects. In
[ScalarExtension](../../Aglib/Algebra/Homology/Amitsur/ScalarExtension.lean), retain
the actual typed objects `S ⊗[R] A` and native algebra tensor maps.
`scalarTensor_eq_native` still identifies this functor with the original
`MonoidalCategory.tensorLeft` by `rfl`. At the first face, compose the original
inclusion and map equations through a short `calc` chain instead of asking
rewriting to reconstruct the hidden colimit objects.

Run `remote-37d1cb4eff6e4d14b893481c5134a0b3`, source
`f204874a98f04592be5ff66d44c0266b4b6d4e2d7a201586f2eb62d9b0e4b87f`,
exposed the failed implicit-transparency boundary. The repaired provider and
actual Coordinates consumer passed in 8.5 and 5.7 seconds in
`remote-a7f7aa6f9de44059b3e32dce7706c6f3`, source
`e76b8b6d4b1b7e7adace25ab99c0fe513ff707809eb974f7310fafa7517a2a4c`.
The separate Comparison consumer was still failing there. The final Amitsur
root subsequently passed in `remote-a31efd3dee9642bc9849f4e6cb6efc59`.
These observations do not isolate a compiler defect or a controlled speedup.
No resource budget or mathematical premise was changed.

