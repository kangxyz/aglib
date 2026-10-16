# Investigating Lean compilation performance

This guide separates measured Aglib bottlenecks from candidate explanations and
records primary-source methods for investigating them. The compatibility basis
is Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. External issue states were checked on
2026-10-16. Historical reports do not establish a defect in the pinned compiler.
[Caching](CACHING.md) owns artifact reuse; this guide concerns the cost of
checking a declaration when compilation is necessary.

## What the measurements establish

The successful [cold CI run](https://github.com/kangxyz/aglib/actions/runs/38711518878)
at `419bd685cee21ac408756fbfe99565be19d186fd` reported 673 seconds for
`Godement.OpenBaseChange`, 378 for `Godement.Section.Span`, and 225 for
`Godement.Tensor`. The twelve slowest modules accounted for about 52% of
reported library task time. That CI run omitted extra independent kernel replay.
Its build helper admitted one external compiler at a time, so scheduling also
contributed to whole-library wall time.

Local declaration profiling distinguishes a different problem inside these
files: kernel checking dominates tactic execution. For example,
`godementTensorTotalUnit_app` spent about 80 seconds in the kernel despite its
proof being `rfl`. This does not establish large instance-search or simplifier
cost. Profiling categories and asynchronous tasks can overlap; their cumulative
times must not be added or treated as wall-time percentages.

The retained changes use explicit object representations and narrowly typed
proof helpers:

- In the Tensor component, the inferred codomain `F.obj (G.obj C)` is compared
  with the same object represented as `(G ⋙ F).obj C`. Explicitly aligning the
  map's source and composite codomain reduced an isolated module measurement
  from 144.58 to 103.82 seconds under the same setup. An isolated type-formation
  probe fell from 35.18 seconds and 10,936,920 unfolding events to less than a
  millisecond and 36 events. These counters describe that probe, not the whole
  module.
- The subsequent archive integration supplies a typed whiskering-component
  equality through `NatTrans.unitPostcompose_whiskerRight_app_of_eq`, retaining
  that object alignment. In its fresh artifact-producing run, Tensor passed in
  60.66 seconds; its component-app kernel task was below the profiler's 100 ms
  display threshold, compared with 43.28 seconds in the prior aligned candidate.
  This run has different output/profiling settings from the isolated module
  comparison, so the wall times are not a controlled speedup ratio. The original
  component equation and its actual rewrite-based quasi-isomorphism consumer
  both pass. The remaining total-quasi-isomorphism task still takes about
  40 seconds.
- Explicit objects and a private equality-transport lemma in OpenBaseChange
  reduced its named kernel probe from 52.14 to 21.16 seconds. The adopted module
  passes, and its public `.olean`, IR and C outputs match the original artifacts.
  The separate baseline timing wrapper failed after a host diagnostic; it does
  not establish a second clean whole-module build or a whole-module speedup.

The combined Tensor, Contraction, carrier and literal archive-consumer checks
pass against the fresh producer artifacts. Existing constructors and canonical
maps are unchanged. Contraction's public `.olean` and runtime outputs also match
the original artifacts; its helpers change proof implementation.

Broad abstraction was less reliable. A generic-constructor Span candidate
compiled faster but failed an actual consumer's reduction proof. Narrower
candidates also failed elaboration or a consumer. Span therefore keeps its
explicit construction, with three additional checks of the original component
formula and quasi-isomorphism hypotheses. A fast generic helper alone is not
evidence that its expensive specialization is fixed.

The full-subcategory boundary in Quillen's `FlasqueThirdSpan` exposed another
expensive conversion: identifying a lifted functor followed by the inclusion
with the raw Godement functor unfolded the large concrete construction. The
general [short-exact-sequence transport lemma](../Aglib/Algebra/Homology/ShortComplex/Subcategory.lean)
instead uses the actual supplied natural isomorphism and the `map_comp` law.
It preserves the original exact functor and its short-exactness certificate.

In two clients importing the same literal source prefix, kernel checking of
the generated exactness proof fell from 85.43 seconds to 0.098 seconds. Peak
resident memory fell from 12.84 to 2.57 GiB for the complete profiled clients;
each client checks both a separate certificate and the record, and detailed
profile export adds substantial overhead. These are controlled client results,
not whole-module speedup or CI resource measurements. The actual changed
`FlasqueThirdSpan` subsequently compiled in a focused Lake run in 219 seconds,
with only that leaf rebuilt. Its complete CI memory fit remains unmeasured.

## Why a short proof can be expensive

The kernel checks the elaborated proof and its type. In particular, it checks
definitional equality by reduction: two expressions can denote the same object
while requiring extensive unfolding to recognize that equality. An `Eq.refl`
proof can therefore be small while checking its use against the declared
equality is expensive. With nested functors, complexes and data-carrying category
instances, the important difference may be an implicit object argument or the
representation of a component's codomain.

The pinned [kernel implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/kernel/type_checker.cpp)
also compares proof types when applying proof irrelevance. Proof irrelevance
does not make conversion of those types free. Distinguish this work from
metavariable unification in the elaborator and from compiling executable code.

## Methods and evidence

| Method | When it can help | Evidence and limits |
| --- | --- | --- |
| Align object, codomain and instance representations explicitly | Different inferred expressions are definitionally equal but expensive to compare | The Tensor experiment above is direct local evidence. Extra annotations that elaborate to identical core terms need not help. Inspect the expressions first. |
| Generate explicit simplifier equality certificates | A `simp` proof leaves expensive reductions implicit | [Lean issue 14331](https://github.com/leanprover/lean4/issues/14331) reports a severe case improved by `simp -implicitDefEqProofs`. The pinned default remains `true`. Test only implicated calls and measure the complete declaration; this is not a direct replacement for a literal `rfl`. |
| Name repeated proof arguments before elaborating the statement and body | Large embedded proofs or differently represented proof types are repeatedly compared | The [primary-author discussion](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/dsimp.20simplifies.20proofs.2C.20which.20is.20slow.html) explains both improvements and regressions. Its 0.06-to-10-second kernel regression concerned an experimental branch, not a demonstrated current compiler bug. |
| Use `as_aux_lemma` for identified duplicated proof terms | Proof bodies are duplicated in generated terms or simplifier results | The [pinned tactic](https://github.com/leanprover/lean4/blob/v4.34.1/src/Init/Tactics.lean#L13-L18) and [Mathlib examples](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Logic/Equiv/Basic.lean#L280-L291) provide the existing mechanism. Smaller terms can still require more conversion; abstraction is not an automatic kernel optimization. |
| Separate construction data from correctness proofs | Repeated large structures or generated correctness terms are the measured problem | Mathlib explicitly splits [projective resolutions](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean#L289-L310) for performance. Preserve the actual component formulas and consumers that unfold them. |
| Preserve useful regular definition boundaries | Kernel reduction order expands a large argument before a small wrapper | [Kernel reduction hints](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Declaration.lean#L17-L47) explain why `def` and `abbrev` can behave differently. Elaborator attributes such as `irreducible` are a different mechanism. True `opaque` data changes the reduction interface and requires deliberate API design. |
| Align parent instances and supply universe information | Diagnostics show instance synthesis or universe unification dominating | These primarily address elaboration. They are lower priority for the current kernel-heavy profiles; the presence of category instances alone does not diagnose an instance diamond. |

An especially relevant open lead is [Lean issue 14803](https://github.com/leanprover/lean4/issues/14803)
and its proposed [PR 14927](https://github.com/leanprover/lean4/pull/14927).
They describe fast elaboration followed by expensive kernel comparison of an
application with its eta expansion. The proposed change tries eta before delta
reduction. The PR was open and unmerged when inspected, and the pinned source
still uses the reported order. This is a diagnostic lead: Aglib's actual
conversion pair must match before attributing its cost to that mechanism.

Similarly, [PR 14770](https://github.com/leanprover/lean4/pull/14770) provides a
concrete wrapper-unfolding example. A merged PR is not sufficient evidence that
its exact implementation is present in a release: inspect the pinned source.
Do not change toolchains based only on an issue title or a historical speedup.

## A focused diagnostic procedure

1. Preserve compiled dependencies, the exact source and package options. Select
   one slow declaration rather than rebuilding the library. Separate imports,
   elaboration, tactic execution, kernel checking and output serialization.
2. Use native `trace.profiler` to identify named kernel tasks. In a scratch copy,
   enable `diagnostics` for the selected declaration to obtain kernel unfolding
   counters. The pinned [declaration checker](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/AddDecl.lean#L183-L191)
   supplies the named `Kernel` trace. Counters identify repeated unfolding, not
   exact per-constant time.
3. Inspect the declared type and inferred proof type, including implicit
   source/target objects, category instances, eta expansions and proof-valued
   arguments. Determine whether forming the type or checking the proof causes
   the expensive comparison. Distinguish a large type conversion from a large
   proof term.
4. Choose one mechanism supported by those diagnostics: matching explicit
   arguments, an explicit equality certificate, a named statement proof, or a
   narrowly factored construction. Preserve mathematical hypotheses, canonical
   maps and the standard heartbeat policy.
5. Compare full declaration/module kernel cost under the same inputs and check
   the immediate consumers. Keep a change only when it improves the relevant
   cost and preserves their required reduction behavior.

Module exposure is part of that last condition. Official [module documentation](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
explains why an imported public definition need not have an exposed body. A
locally successful rewrite can therefore fail downstream. Export useful
component equations when the interface needs them; do not compensate with
blanket `import all` or global exposure changes.

Caching reduces repeated work; parallel scheduling can reduce whole-build wall
time. Neither makes one pathological kernel conversion cheaper. Raising
heartbeats, adding more threads, changing `simp` indiscriminately or replacing
every `def` with `abbrev` is not a supported remedy for these observations.
