> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#values-at-concrete-fibre-products-over-spec-commringcatof-a) · [Context](original-context.md) · [Case index](README.md) · [Previous record](placement-edits-in-widely-imported-modules.md) · [Next record](declaration-lint-memory-in-ci.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Values at concrete fibre products over `Spec (CommRingCat.of A)`

In the flattening-stratification work of 2026-10-19, kernel checking was slow for declarations
whose values or proofs involve a fibre product over `Spec (CommRingCat.of A)`, such as
`pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))`. Retained probes on the pinned toolchain
against compiled dependencies, at profiler threshold 50 ms, measured the following.

- The definition `moduleCohomologyGlobalScalars (pullback p (Spec.map (CommRingCat.ofHom σ))) N q`,
  at its inferred type, took 3.2 seconds of kernel type checking. The same definition over
  `pullback p g`, with `g : Z ⟶ W` variable, stayed below 50 ms.
- The same terms inside theorem binders (`theorem probe (_h : P) : True`) checked in about 13 ms
  together for `pullback p (Spec.map _)`, `pullback p g` and `P^n_A ×_{Spec A} Spec B`, including
  `Module.Projective B` of `H^q` with its structural action.
- Restating the base-change part of `IsFiberBaseChangeBound` at one point and proving it by
  projection from the bound took 16 seconds; the vanishing part took 12 seconds. The same
  proposition as a theorem binder stayed below 50 ms.
- In `FlatteningStratification/Flatness`, the uniform comparison lemma took 28.6 seconds and
  `directImageTwistSectionsLinearEquiv` 8.1 seconds.

The diagnostics counters for such declarations are dominated by additive-structure projections
(`Functor.obj`, `AddCommGrpCat.str`, `AddGroup.toSubNegMonoid`, `DFunLike.coe`) and include
`Function.Injective.addCommGroup` several thousand times; Mathlib transports the group structure
of `Ext` along `homEquiv`. The conversion pair has not been identified. A candidate mechanism,
unverified: the kernel compares two presentations of the additive structure on `Sheaf.H`, and
with a concrete base the delta order unfolds `Spec` and fibre-product data.

Forming statements over concrete fibre products is cheap; checking values and restated proofs
over them is not. Let one theorem consume the defining hypothesis directly, keep restatements and
definitions at `Spec (CommRingCat.of A)` few, and state helpers at variable data, as in
`PullbackComposition`. Before attributing a cost to a fibre product, separate statement
formation from proof checking with a theorem-binder probe.

