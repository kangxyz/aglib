# General Milnor flatness descent

`Aglib.RingTheory.Etale.MilnorPatching.Flat` extends the frozen component
reconstruction in `General`. It keeps the original literal fiber base
\(P=R\times_T S\), with \(f:R\to T\) surjective and \(g:S\to T\) arbitrary.

`flat_of_component_baseChanges` proves that an arbitrary \(P\)-module \(M\)
is flat when \(R\otimes_P M\) is flat over \(R\) and \(S\otimes_P M\) is
flat over \(S\). The module may have arbitrary rank and a different universe
from the three rings. No finite-generation, Noetherian, nilpotence, or
faithfulness condition is present.

`flat_fiberMap` applies this criterion to the original seven-map square.
Its two component identifications are the canonical equivalences from
`General`, with the prescribed pure-tensor formulas. It assumes the original
compatible boundary tensors, surjectivity of \(f\), and flatness of \(r\)
and \(s\); it proves flatness of the original `fiberMap`.

## The lower restricted tensor criterion

The generic statements are owned by
[Flat/KernelCriterion](../../Flat/KernelCriterion.md), independently of Milnor rings.

For a surjection \(A\to B\) with kernel \(J\), the theorem
`Module.Flat.rTensor_injective_of_flat_baseChange_of_annihilated_cokernel`
assumes that \(B\otimes_A M\) is \(B\)-flat and the original inclusion
\(J\otimes_A M\to A\otimes_A M\) is injective. It proves tensor
injectivity for an injection whose cokernel is annihilated by \(J\).
The compatible quotient action is constructed internally.

The proof uses a free presentation of \(M\). A presentation diagram first
gives injectivity after tensoring its kernel inclusion with \(B\).
The flat-quotient tensor theorem over \(B\), canonical tensor cancellation,
and the same presentation diagram then prove the restricted conclusion.
The diagram lemma generalizes the native argument in
`Mathlib.RingTheory.Flat.Equalizer`. Keeping its presentation abstract avoids
unfolding a concrete free-module map during the diagram application; all
declarations compile at the standard heartbeat limit.

## Use of both Milnor components

Put \(J=\ker(P\to S)\). The explicit `conductorEquiv` identifies \(J\)
with \(\ker f\) by the first coordinate. First-component flatness implies
injectivity of \(J\otimes_P M\to M\) after composing with
\(M\to R\otimes_P M\).

For an ideal \(a\subseteq J\), let \(A\subseteq R\) be the ideal generated
by its first coordinates. The actual map \(a\to A\) is injective, and its
cokernel is killed by \(J\): multiplication by a conductor element turns
each \(R\)-coefficient into the first coordinate of an element \((c,0)\in P\).
This is proved by span induction. The restricted tensor lemma applies, and
first-component flatness then gives the tensor injection for \(a\to P\).
For an arbitrary ideal \(a\), second-component flatness and the exact
sequence involving \(a\cap J\) reduce the tensor injection to that case.
The ideal criterion concludes flatness.

The primary mathematical route is
[Stacks 0D2I](https://stacks.math.columbia.edu/tag/0D2I); the restricted
annihilated-cokernel step corresponds to the exponent-one part of
[Stacks 051C](https://stacks.math.columbia.edu/tag/051C). These sources were
inspected on 2026-10-21. The Lean proof uses the displayed native maps and
tensor exactness, without importing a source theorem as an assumption.

The finite-presentation and universal etale conclusions are owned by
[FinitePresentation](FinitePresentation.lean).
