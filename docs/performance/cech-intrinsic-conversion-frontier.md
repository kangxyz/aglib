# Čech intrinsic comparison: conversion frontier

## Question, status and source identity

Which declarations and phases dominate the already-passed Scheme
`Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison`, and does the evidence
justify a bounded existing-proof pilot? This case records the completed single
diagnostic and the current frontier. A repair and speedup are not established.
The mathematical implementation and source review are retained inputs, separate
from this documentation's production validation.

The native basis is HEAD `54d6974ace11bf7d197aa925cb8cade86db8a24f`,
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Scheme Comparison has SHA256
`a9ff484188f60dc58dfe142249bc28ed0cf9fbde1280020dba63d2c5b9a76e8a`;
Modules has SHA256
`e3776bb971ea3943fcc010812ed309358d46d7149a2e70b401d903ee1d192f3c`.
The diagnostic source-content vector is
`94ff0139b4121437ff5e1fe111ffcf557a15e479e541a51a1506045fdc2721a8`.
The [support capsule](cases/cech-intrinsic-conversion-frontier/README.md) retains
the actual nine-file source, source vectors, review packet, requests, setup,
receipt/logs, extraction script, complete structured timings and exact excerpts.
Its [manifest](cases/cech-intrinsic-conversion-frontier/manifest.json) records
hashes and full raw-evidence locators.

The nine implementation files have source-matching scoped native passes,
retained incrementally across six captures. Five whole commands had mixed
results; those are not whole-run passes. The ordinary Scheme Comparison pass
was displayed as 155 seconds in `fa261c799e6541b9a68d7543dc7fb23c`; the
Modules e377 pass was displayed as 193 seconds in
`70c27e125c914672b7347ca866b14b5e`. These are retained native observations,
not matched benchmarks or normal per-file RSS measurements. No whole-library,
standalone lint/test or axiom verdict is supplied by this case.

## Preserved mathematical and implementation conditions

The shared producers retain the original Čech complex, product intersections,
alternating signs, literal row/column augmentations, one totalization,
constant-integer section values and original HPrime/H normalization. The
stalk contraction is topological. Generic column exactness takes actual
resolution-section exactness; canonical comparison requires an actual cover
and positive original open-Ext acyclicity. Scheme quasicoherence,
affine-intersection and separated affine-cover hypotheses remain genuine.
No replacement nerve, quotient or resolution family is introduced. Canonical
module AddEquiv/LinearEquiv select one resolution internally; old public types
and legacy supplied-resolution value data remain through the compatibility
and independence boundary. These are the accepted implementation packet's
conditions, not new mathematical conclusions from profiling.

## One instrumented run

Native run `remote-6536a79189ea41d098aedfdb4272f3a9` used the exact a9ff
source, pinned module/dependencies, default source budgets and runtime options
`-Dtrace.profiler=true -Dtrace.profiler.threshold=100` (100 ms display threshold).
It had one observed frontend, exit 0, 641.305 seconds wall time and
66,793,397 bytes of stdout. The native owned-tree peak was 2,355,453,952 bytes
(about 2.19 GiB), with 4 compiler threads, 12800 MiB frontend heap and the
normal 2-job/32768-MiB admission profile. This resource observation belongs to
the diagnostic's owned tree.

The original production setup had been cleaned. Request v2 explicitly replaced
that unavailable input with mechanically regenerated pinned setup; the earlier
request did not authorize a second frontend. `lake --no-build setup-file`
started zero compilers. Reconstructed setup SHA256 is
`1f0adc79ba795e65b54db2f53e679690f57b51a999495f3ededacfb42099a159`.
Original-setup byte identity is unavailable and is not claimed. Exact commands,
options and provenance are in the retained runtime and preparation JSON.

## Observed intervals

Source lines refer to the frozen `diagnostic/source.lean`; trace lines refer
to authoritative full stdout. These named inclusive intervals may overlap.

| Declaration | Source line | Kernel interval | Trace line |
| --- | ---: | ---: | ---: |
| `moduleHPrimeTopAddEquiv_scalar` | 249 | 16.698 s | 91094 |
| `sheafHPrimeTopAddEquiv` | 96 | 16.485 s | 54622 |
| `module_additiveResolutionHomologyEquiv_scalar` | 428 | 15.259 s | 151177 |
| `resolutionSectionShortHomologyEquiv` | 410 | 13.340 s | 144888 |
| `additiveResolutionHomologyEquiv` | 298 | 13.131 s | 118033 |
| `moduleCechCohomologyAddEquiv_scalar` | 740 | 11.661 s | 216969 |

Other named Kernel intervals include canonical module comparison (10.734 s),
its supplied-resolution view (10.224 s), equality-to-canonical (10.108 s), and
resolution independence (9.970 s). Value elaboration has a different visible
frontier: `subsingleton_sheafHPrime_of_moduleResolution_sections_exact`
(36.434 s, trace 67143), `geometricCechRowAugmentation_naturality`
(23.258 s, trace 336071) and
`moduleResolution_openKernelSections_surjective` (13.849 s, trace 65857).
The complete structured projection and fixed sorted selections are retained,
including header and instance-search observations.

## Supported next pilots and remaining mechanism gap

Repeated `(sectionsFunctor X U).PreservesZeroMorphisms` and
`G.PreservesZeroMorphisms` synthesis took 5.045, 5.028 and 5.011 seconds
(trace 67127, 65850, 66384). Trace 71175–71220 compares the actual sheaf
full-subcategory zero dictionary with the preadditive zero dictionary;
one nested comparison is about 2.33 seconds. This supports a bounded pilot
supplying the already proved preservation witnesses at the literal
Scheme/module and additive-sheaf category/zero heads, in the smallest local
scope covering headers and bodies of
`moduleResolution_openKernelSections_surjective` and
`subsingleton_sheafHPrime_of_moduleResolution_sections_exact`.
The original `sectionsFunctor` already uses
`SheafOfModules.additiveEvaluation`; reuse its existing arbitrary-zero witness
and the [validated dictionary method](native-evaluation-zero-dictionaries.md).
The observation does not measure the pilot's benefit. No new hypothesis,
functor, global priority or budget follows from it.

At `sheafHPrimeTopAddEquiv`, trace 142–174 compares Scheme carrier and
`X.toTopCat` presentations; nested trace 179–1130 passes through Ext's
additive structure, `Ext.homEquiv`, `Localization.SmallHom.equiv` and
`equivShrink`. Together with the short adapter's 16.485-second named Kernel
interval and its scalar consumer's 16.698 seconds, this warrants inspecting
one native site/Ext/additive presentation and its actual scalar consumer.
Preserving the whole generic comparison head is a candidate pilot. The exact
kernel reduction pair, type-versus-value contribution, causal mechanism, cost
movement and speedup remain unresolved. Elaboration conversion evidence does
not itself identify the expensive kernel conversion. Dropping all result
types or changing every `def`/`abbrev` is not supported by this evidence.

The author is staging small repairs separately. This frozen case does not
adopt those changed inputs or claim they succeeded. A later result must bind
its changed source and actual affected consumer; it must not relabel this
one diagnostic as evidence for a later repair.

## Interpretation, archival boundary and reproduction

Do not sum nested/async intervals or allocate the ordinary 155 seconds from
this profile. The 641.305-second instrumented wall time is not a matched
comparison, ratio or regression measurement. Trace-production cost was not
separately measured. Large command/async frames can include waits for kernel
tasks. No adequately labelled import/serialization breakdown was visible;
this does not establish zero cost there. Normal per-file RSS is unavailable.

The authoritative full raw trace remains at the durable research-workspace
locator in the capsule manifest, with SHA256 `bc407f9755a0321e3bcf78280788a0215023716326abe66642c9d1c4597d4f38`.
The capsule retains exact necessary excerpts and the complete structured
projection instead of copying 66.8 MB of redundant rendered trace. Full raw
logs/source manifests at the external locators remain part of the evidence
and must be preserved; the capsule does not claim standalone raw-trace closure.
Run only the existing analysis with `python3 analysis/analyze.py` from the
capsule directory to reproduce its extraction using the retained workspace
trace. This invokes no Lean. No new compiler, profile, tests or audit ran for
this writing product. Document/source correspondence, hashes, JSON and links
are production validation; mathematical acceptance remains separate.
