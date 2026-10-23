# Completed local rings after base change to a completion

Import `Aglib.RingTheory.AdicCompletion.FiniteTypeLocalComparison`.

Let `I` be a finitely generated ideal of a commutative ring `A`, let `B` be
an arbitrary commutative `A`-algebra, and write `Ahat = AdicCompletion I A`.
For an ideal `J` of `B` containing the image of `I^n`,
`AdicCompletion.quotientTensorCompletionEquiv` constructs

```text
B/J ≃ (Ahat ⊗[A] B)/(J.map includeRight).
```

Its value on the class of `b` is the class of `1 ⊗ b`. Thus this is the
comparison from the original coefficient map, with its specified quotient
square. It does not replace that map by an abstract isomorphic algebra.

The proof first handles an `A`-algebra `C` killed by `I^n`. The canonical
projection `Ahat → A/I^n` defines the coefficient map to `C`. Every completion
element is congruent modulo the extended `I^n` to an element of `A`, because
`I` is finitely generated. In `C ⊗[A] Ahat`, that difference vanishes, so the
tensor product is canonically `C`. Apply this construction to `C = B/J` and
the native tensor-quotient equivalence.

The underlying evaluation map and equivalence are also available as
`nilpotentCoefficientMap`, `nilpotentTensorMap` and `nilpotentTensorEquiv`.
`nilpotent_includeRight` identifies the completed coefficient with its finite
evaluation in the tensor product, and `nilpotentTensorEquiv_symm_apply` records
that the inverse equivalence is the original tensor inclusion.

The current consumer is the closed-fibre completed-local-ring comparison of
Stacks, Lemma 54.11.1 ([0BG5](https://stacks.math.columbia.edu/tag/0BG5)). The
algebraic quotient comparison requires no finite-type, Noetherian, normality,
excellence, or finite-module assumption on `B`. A Noetherian local base supplies
finite generation of its maximal ideal. If that ideal maps into a prime `p`
of `B`, its `n`-th power maps into `p^n`, so the theorem applies at every
power of `p`.

For an actual ideal `q` of `Ahat ⊗[A] B` containing the extended base ideal,
`tensorClosed_map_comap` proves

```text
(q.comap includeRight).map includeRight = q.
```

The proof approximates each target element by an original coefficient modulo
the extended base ideal. It applies to all such ideals, and in particular to
the prime of an actual closed-fibre point. Write `p = q.comap includeRight`.
`tensorPowerQuotientEquiv` then constructs `B/p^n ≃ (Ahat ⊗[A] B)/q^n` for
every `n`. Its `_mk` and `_factor` theorems retain the original coefficient
map and compatibility with the native power-quotient transitions. The case
`n = 1` retains the original `B/p` comparison as well.

`localizedPowerQuotientEquiv` transports these equivalences along the original
prime-complement monoids. Mathlib's quotient-localization instance identifies
the resulting rings with the actual quotients of `B_p` and `T_q`, where
`T = Ahat ⊗[A] B`. `localMaxPowerQuotientEquiv` expresses the same comparison
using the maximal ideals of these actual local rings. Its
`_localRingHom` theorem gives the square with the original
`Localization.localRingHom` on every local element. This also proves
compatibility with all maximal-power quotient transitions.

`tensorLocalCompletionsEquiv I B hI q hclosed` constructs

```text
AdicCompletion (maximalIdeal B_p) B_p
  ≃+* AdicCompletion (maximalIdeal T_q) T_q,
```

Here `tensorComparisonRingHom I B` is the underlying ring homomorphism of
the original `includeRight`, and `p = q.comap (tensorComparisonRingHom I B)`.
Its `_eq` and `_apply` theorems retain that original map. The same ring-map
definition is used throughout the prime, localization and completion interfaces.
The completion equivalence inherits its return type directly from
`localCompletionsEquiv`, so the maximal ideals and completions use the same
native commutative-ring presentation of each prime localization.
`atPrimeCompletionMap` is the native completion `algebraMap`, with its
`_eq` theorem. Both the generic and tensor completion squares use that same
typed ring map, retaining the completion-algebra presentation as well.
The `_algebraMap` theorem proves, for every
`x : B_p`, that its original completion image maps to the completion image
of `Localization.localRingHom p q includeRight rfl x`. The construction
uses `liftRingHom` in both directions, proves the two original ring-map
composites equal to the identity by finite-order evaluations, and then applies
`RingEquiv.ofRingHom`. Thus no completion-isomorphism oracle is supplied.
The first-order comparison retains the original residue quotients as well.

The hypotheses remain: `A` is commutative, `I.FG`, `B` is a commutative
`A`-algebra, `q` is prime, and the image of `I` in `T` lies in `q`.
No Noetherian or finite-type hypothesis on `B` is required for the comparison.
The current surface consumer supplies a Noetherian local base and a
finite-type coefficient algebra, but those extra premises are not used here.

The scheme-stalk and literal pullback-point wrapper remains a separate
obligation. No preservation of normality under arbitrary completion is
asserted.
