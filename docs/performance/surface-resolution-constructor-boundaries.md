# Surface-resolution constructor boundaries

These four cases retain repairs recorded during surface-resolution work based
on Aglib `f27c5fa9b8f76147e16caacf52f56f26eabddb87`. The notes were
uncommitted on that research HEAD; the individual tested source hashes and
runs below identify the actual compilation evidence. Declaration names identify
the original implementations; they do not require a particular release's
selection of source files. The observations use Lean 4.34.1 and Mathlib
`d13f23b7`, with standard budgets. No heartbeat, recursion, transparency or
other option was raised for these repairs. No profiling, separate client check
or kernel replay was added.

The common method is to retain the original map or constructor and prove its
needed equation at a complete variable boundary before specializing. The
boundary differs in each case: an original ideal inclusion, a coefficient
calculation, elementary typed linear maps, or a whole localization-and-kernel
producer. Abstracting an incomplete part can leave the same concrete
conversion in the consumer.

## Zero-power comparison: make the original inclusion the forward map

In `Exceptional.Powers`, source `23bd337f` reached a native kernel timeout in
`ordinaryPowerZeroIso_hom`. A missing-constant cascade followed in its
degree-zero consumer (`remote-40956064`, whole module 180 seconds). Concrete
normalization of the forward map of a transported comparison had left the
power and transport constructors in the comparison.

The repair first proves `ordinaryPowerZeroInclusion_isIso` for the original
ideal inclusion. It transports invertibility from the top ideal using the
zeroth-power equality, then defines `ordinaryPowerZeroIso` with `asIso` on
that same inclusion. Consequently, `ordinaryPowerZeroIso_hom` identifies the
forward map with `idealInclusion ((exceptionalIdeal A hd) ^ 0).subschemeι`
by `rfl`. The original restriction/unit calculation consumes that identity
without unfolding the transported power constructors.

Whole source `e820d1eb` passed in `remote-2088b6dd` (39 seconds), including
the original degree-zero normalization and all power/product consumers.
The original map and mathematical premises are retained, including the
dimension-two input and the original Nagata and rational-vanishing inputs
where the degree-zero consumer requires them. Other reported proof errors
were also repaired; the two durations are not an isolated timing comparison.

## Surface dual unit: separate the coefficient identity from geometry

`NormalSurface.Cohomology.UnitTrace` source `c06e1e70` exhausted the standard
200000-heartbeat budget in its coefficient/Ext-zero calculation
(`remote-7617d011`, whole frontend 60 seconds).

The retained `original_coinduced_zero_precomp` proves the coefficient identity
on variable modules and the original augmentation. Typed single, zero-shift,
Ext-zero and inverse-isomorphism equations establish this identity before
the geometric theorem composes it with the original unit naturality square.
Small generic composition lemmas avoid unfolding the full concrete
linear-equivalence constructors at that specialization.

The intervening source `aeb5c408` failed only at a remaining typed zero-shift
cancellation. Native associativity and inverse-isomorphism laws repaired that
step. Whole source `f3d62d7a` passed in `remote-ab2b3cea` (32 seconds),
including the original dual-unit, section and trace consumers. All original
maps, coefficient actions, hypotheses and standard budgets are retained.
Other proof repairs also changed, so these durations do not measure a
controlled speedup.

## Two-layer annihilator: prove elementary linear arguments before specialization

The native `TwoLayer.Annihilator` consumer reached the default recursion limit
when proving exactness after its concrete Ext equivalence and when applying
the concrete boundary's scalar law (source `1b1d2728`,
`remote-ab2b3cea`).

The repair proves these elementary arguments for variable typed linear maps
and a linear equivalence in
`annihilator_exact_surjective_linearEquiv_comp` and
`annihilator_scalar_of_exact_image`. It then specializes to the original
homology, coefficient and Ext carriers. This preserves the actual boundary,
its A-action and the original hypotheses without expanding nested derived
constructors inside the elementary proofs.

Whole source `e2c68901` passed in `remote-ea7fa93c` (8.9 seconds). No
recursion, heartbeat or other option was raised. This is coverage of the
repaired source, not a controlled performance comparison or a separate
acceptance of its mathematical consumers.

## Centered Case-II kernels: abstract the complete algebraic producer

In `DoubleLine.Marked.Chart`, source `d4431ade` exhausted the standard
200000 heartbeats at `whnf` in `centered_kernel_of_linear_prime` and
`centered_kernel_of_origin` (`remote-9481d38f`, whole frontend 57 seconds).
Abstract coordinate helpers and a regular exact-kernel proposition had not
closed the concrete saturated-chart specialization.

The retained private
`Ideal.localTriple_linearSquareKernel_of_other_difference` performs the
whole lift decomposition, original localization map, coordinate shear and
canonical-kernel transport over a variable source ring `S`. For a prime
`P`, it receives both original presentations
`P = Ideal.span {t, q, v}` and `P = Ideal.span {t, u, v}`, the difference
condition `q - u ∈ Ideal.span {t, v}`, and the original homogeneous linear
form `L` whose squared span is the first triple's cotangent kernel.
It decomposes the difference into the two generators, uses the original
`algebraMap S (Localization.AtPrime P)` to prove the shifted-coordinate
equation, and transports that kernel to the second triple. Both boundaries
retain `HasLinearSquareCotangentKernel`.

Each actual chart supplies its original prime-span and reduction-kernel facts
once. The linear-prime consumer retains `q = X - Polynomial.C (residue A α)`
and its recentered chart; the origin consumer retains `q = X`. Each proves
the lift difference from the original reduction map's kernel before invoking
the complete producer. Original polynomials, primes, scalar, reduction and
residue maps, and mathematical hypotheses are unchanged.

Whole source
`a43c4f72192ccf225257c3ed4c54e503219828741f4888447cd30d243c009aaa`
passed in `remote-b63ad85e` (41 seconds), with the same pins and standard
budgets. This establishes repaired-chart coverage, not a controlled speedup
or a sole compiler cause.

At that run, the marked successor failed separately and the whole Case-II
and scheme assembly remained open. A later successor pass was recorded as
source `3d24` in `remote-1e7adcdb` (116 seconds). That is distinct downstream
coverage; it supplies no tested performance-cause attribution for the chart
repair and does not by itself close the whole Case-II or scheme assembly.

## Evidence boundary and practical use

Use the smallest complete boundary that preserves the actual consumer's
maps, hypotheses, actions and reduction interface. First identify whether the
consumer needs the literal original forward map, a coefficient equation, an
elementary linear argument, or the entire algebraic construction. Prove that
boundary over variables, then supply the original concrete data once.

The run and source identities above preserve existing evidence; documenting
them adds no new compilation, benchmark or acceptance run. Changed proofs and
uncontrolled cache/load conditions prevent a controlled speedup claim. A
whole-module pass covers that module on its recorded source basis; it does
not establish unrecorded downstream closure, a unique compiler mechanism or
independent mathematical acceptance. Current commands and validation scope
remain with [development](../DEVELOPMENT.md#local-verification-and-ci) and the
[repair workflow](../PERFORMANCE.md#repair-workflow).
