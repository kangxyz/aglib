> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-one-representation-of-module-sections) · [Context](original-context.md) · [Case index](README.md) · [Previous record](generated-import-entries-and-file-length-limits.md) · [Next record](preserve-regular-equations-through-conormal-comparisons.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Keep one representation of module sections

On 2026-10-23, the initial arbitrary-section nonvanishing implementation
reached the standard 200000-heartbeat limit at `whnf` while elaborating
restriction composition. This was an elaboration timeout. The accepted
[Nonvanishing](../../Aglib/AlgebraicGeometry/Modules/Invertible/Nonvanishing.lean)
implementation states the comparison using one explicitly typed
`M : X.Modules`, changes the goal to its actual presheaf morphisms, and
applies the functor law:

```lean
change (M.presheaf.map (homOfLE k).op ≫ M.presheaf.map (homOfLE h).op) s =
  M.presheaf.map ((homOfLE k).op ≫ (homOfLE h).op) s
rw [Functor.map_comp]
```

This avoids asking elaboration to identify differently presented section
carriers while also reconstructing the composite restriction. In related
scalar and zero-section proofs, give `L.val` an explicit `X.Modules` alias
before using `.presheaf`, and retain that same `M.presheaf.map` expression
through the calculation. The bare expression `L.val` has syntactic type
`SheafOfModules`; switching representations in the last step introduced
field-projection errors or unnecessary conversions.

The original candidate `93b8d319` failed in native run
`remote-b5b40b72db8f4d7398c2fb40e082f3d3`. The complete repaired module,
SHA-256 `0b00b8a1d47a07013706469cf05ce96e797ffd3e759da8701aafbc045987b590`,
passed ordinary native compilation in
`remote-9fcb2011c37746649cfe2ac83c040e1a`: one compiler invocation and
11.14 seconds for the remote build action. All declarations retained the
standard heartbeat budget and their original maps and hypotheses. Several
proof repairs and cache conditions differ between the runs, so these
observations establish removal of the timeout, not a controlled speedup
ratio or a general attribution of compilation cost.

When the same boundary occurs elsewhere, align the actual module object,
section carrier and morphism presentation before applying a narrowly typed
naturality or composition lemma. Record the successful ordinary producer
compilation and its actual consumers under [normal proof iteration](../DEVELOPMENT.md#normal-task).

