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


### Pin the affine ring carrier before checking the original local trace square

The source names, hashes and checks in this section identify historical executions;
they do not attest to subsequently refactored sources.

On 2026-10-30, a legitimate lower exterior-power extraction invalidated the
original relative projective trace. Rechecking the unchanged 1257-line
`Trace/Core.lean` (`69630ea174686f1c79f3e3acf90349bf97318eba27195bddcd536d07faf4b6f2`)
hit the process-group memory guard. A focused invocation with a smaller Lake
process also failed; driver overhead alone did not account for the failure.

A bounded sidecar-marker diagnostic retained every original declaration and
located the frontier at `relativeAffineTraceLocal_square` (original line 963).
The original source was then factored once into
[Trace/AffineLocal](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Trace/AffineLocal.lean)
and [Trace/Core](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Trace/Core.lean).
This retained each implementation once, the same namespace, module options,
standard derived-category instances and original public interfaces. The lower
module passed, but the tail still failed. A second bounded diagnostic showed
that the identity equation, its transport and the native comparison all
elaborated before the final `exact hs`; no following declaration marker was
reached. This did not by itself distinguish final elaboration from kernel work.

One explicitly authorized, target-local aggregate-reserve calibration kept
Lean's heap at 7000 MiB and one thread, while allowing 7919 MiB aggregate RSS
within the runner's native physical-memory reserve. It failed with the named
`(kernel) excessive memory consumption` error on the square. Its guard did not
fire. This was diagnostic evidence, not a successful repair or a standing
budget increase; the accepted check below used the original aggregate limit.

The retained square proof destructs `A : CommRingCat` once with
`cases A with | of A =>`. It then uses the literal `Spec (.of A)` throughout
the original identity/transport argument. Before this change, the geometric
maps used `Spec A`, while the affine trace used the carrier `(A : Type u)` and
its rebundled `Spec (@CommRingCat.of ... (CommRingCat.commRing A))`. The
neighboring original affine-normalization proof already used this constructor
elimination. The square also instantiates `traceCanonicalLocalEquation`
directly against the actual goal before proving its identity premise, letting
the goal infer the original source and target trace arrows. The original
statement, trace maps, coefficients, pullback data and hypotheses are unchanged.
No replacement scheme, derived model or additional compatibility premise is
introduced.

The file boundary needed thirteen existing names to cross it. In particular,
the original affine higher natural isomorphism remains opaque, and its original
whole-isomorphism and component equations are public. The tail uses these
proved equations and `affineHigherCompositeFactory_hom`; it does not unfold the
private affine construction. The lower declaration signatures and mathematical
bodies agree with the original source. Two newly public equations use `by rfl`
instead of bare `:= rfl`, avoiding automatic exported definitional-equality
registration against opaque definitions while retaining the same proof.

The failed approaches remain relevant:

- Replacing transport of the whole square by trace-value congruence did not
  make the original unsplit module fit.
- Literal alignment of the final coefficient and removal of whole-goal
  restriction simplification did not make the tail fit.
- Moving the original identity proof to an opaque helper also failed; its
  aggregate-only cutoff did not locate the helper versus main-theorem frontier.
- The module cut and goal-directed comparison alone did not suffice.
- Two new expanded public component equations, one direct factory `rfl` and
  one obtained from the whole-iso equality, failed before lower-module
  completion. Their exact failing declaration was not diagnosed. Restoring
  the original proof shapes and exposing only the necessary original equations
  recovered a fitting lower module; this is not a matched timing comparison.

The accepted lower source is
`facaeb93fbb2e8f634d74b62357c884ac0b3248813abcad3f634efb923169ebd`
(native 183 seconds). The accepted Core source is
`c16fc467dd23cf11cf82a3c75d744a26cfb67217aad6b1b5e63ee92d425d298f`
(native 168 seconds). The retained `build-core-carrier/graph-build.json` receipt
records exit zero, no guard failure, a closed owned process group, 171.99 seconds
wall time, and peak aggregate RSS 7,461,433,344 bytes, with Lean heap 7000 MiB,
aggregate limit 7168 MiB and one frontend/thread. Exact source hashes were
checked again after completion. Logs, marker sidecars, original sources and
failed candidates are retained under the task's `surface-resolution-state`
directory (`trace-core-diagnosis/`, `build-core-tail-local-reserve.log`, and
`build-core-carrier.log`).

These observations establish acceptance of the actual lower and tail modules.
They do not identify a unique kernel conversion pair, isolate the benefit of
constructor elimination from the retained earlier proof boundary, or supply
acceptance of every downstream consumer. Preserve the accepted source and
artifacts rather than launching an additional benchmark or kernel replay.
