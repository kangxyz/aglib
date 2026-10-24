> [Case index](README.md) · [Methods](../PERFORMANCE.md#instances-and-universes).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Field-point cohomology dimensions: specialize residue fields through variable-field statements

In the Picard-strata fibre-condition work of 2026-10-24 (Lean 4.34.1, Mathlib
`d13f23b`, remote builder with 8 frontends × 4 threads, profiler threshold 2–3 s):

- Run `remote-35c0d6936bff422cb0e587b07fc59a2c`: the generic lemmas on
  `moduleCohomologyDimension b M q` (dimension over a variable field `K` for
  `b : Y ⟶ Spec (CommRingCat.of K)`) took 11–29 s of kernel type checking each (definition 14 s,
  `_congr` 16.9 s, `_eq_of_isIso` 22.2 s, `_fieldBaseChange` 22.4 s, two `rfl` comparisons with the
  point-fibre API 12.3 s and 11.5 s, the pasting transport 29.1 s; 129 s of type checking in a
  135 s module build).
  `fiberTwistDim_eq_zero_iff`, stated at the residue field `κ(t)` and proved by
  `Module.finrank_eq_zero_iff_of_free` with a finiteness instance obtained at `κ(t)`, took 68.4 s.
- Restating that lemma at a variable field (`embeddedFiberTwistDim_eq_zero_iff`, 43.9 s) and
  specializing by instantiation reduced the Picard leaf from 71–87 s (three builds of successive
  versions; in the profiled 87 s build this declaration took 68.4 s of 70.2 s type checking) to
  10 s (runs `remote-c6f61f5aa46a4f29bfc05d7834556f59`, `remote-317478057c5340a58185796d1c8252b0`);
  the variable-field lemma itself still costs 43.9 s, once.
- Candidate mechanism, not measured: the kernel compares two presentations of the ring and
  additive structures (the `Field` instance of `κ(t)` and its bundled `CommRingCat` structure;
  the additive structure of `Sheaf.H`), as in [Values at concrete fibre products over
  `Spec (CommRingCat.of A)`](values-at-concrete-fibre-products-over-spec-commringcatof-a.md).
- Rule: state field-point lemmas at a variable field and data, and reach residue fields only by
  instantiating them; do not re-derive finiteness or dimension facts at `κ(t)`. The rule avoids
  repeating the cost at `κ(t)`; it does not remove it: the variable-field lemmas in
  [`Cohomology/Fibers/FieldPoint`](../../Aglib/AlgebraicGeometry/Cohomology/Fibers/FieldPoint.lean) still cost 11–29 s each.
