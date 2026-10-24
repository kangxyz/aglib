> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#binary-form-section-and-geometric-point-typing) · [Context](original-context.md) · [Case index](README.md) · [Previous record](historical-selected-origin-lint-measurements.md) · [Next record](typed-evaluation-of-coefficient-map-composites.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Binary-form section and geometric-point typing

On Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, the new
`ProjectiveSpace.BinaryFormProduct.Fibers.surjective_of_geometric_point_lifting`
proof exhausted 200000 elaborator heartbeats at `whnf` in
`remote-e0d45d58b1ae4817876f8ce2b2f66f61`. The final application of
`Scheme.fromSpecResidueField_apply` had only inferred arguments. The successful
proof explicitly names the point obtained through the original
`Spec.algebraMap`, supplies the original residue point and both explicit
arguments to the native lemma, and annotates categorical pullbacks occurring
inside `Finite` as `: Scheme`. The latter annotations prevent elaboration
through the category of types. The scope owner recorded the unchanged geometric criterion compiling
in 4.7 seconds in `remote-b24285e7546a4c7ba4ad15c6087a07db`.

The same run exposed a separate `Lean.Meta.acLt` heartbeat failure in
`BinaryFormProduct.LocalCoordinates.transitionUnit`, where
`simpa only [mul_comm] using hzw` compared concrete section-ring products.
The exact term `(mul_comm w z).trans hzw` proves the same inverse identity.
The scope owner recorded `LocalCoordinates` compiling in 5.1 seconds in
`remote-095c0a8fd69f4c3aa97f9e7764122554`. The upstream
[simplifier implementation](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Simp/Rewrite.lean)
shows permutation-rule ordering through `acLt`; that current source supplies
background, without establishing a defect or an applicable upstream fix in
the pinned compiler.

The final finite/surjective endpoint batch
`remote-36e7150d5e5e4dce8167addfc4fc81ed` compiled four changed leaves with no
diagnostics on source digest
`a2769aeb58683a14eaaa45e52a11d27d1bed2555759e5afd58e007bd8bd13a8f`.
All original maps, universes and mathematical conditions are retained, with
the standard heartbeat budget. These are successful proof repairs, not a
matched benchmark or a compiler-defect diagnosis; no extra acceptance run
was used.

