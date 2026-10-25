> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#remote-resource-calibration-on-the-unchanged-library) · [Context](original-context.md) · [Case index](README.md) · [Previous record](affine-refinement-through-literal-mate-types.md) · [Next record](historical-selected-origin-lint-measurements.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Remote resource calibration on the unchanged library

A Linux trial on 2026-10-19 used committed source
`b001ca8814edba7b56866202765094b724ad0c9e`, the pinned Lean 4.34.1 and Mathlib,
32 available CPUs and a cgroup memory limit of 120 GiB. Matching Mathlib outputs
were recovered first; Aglib started without compiled project outputs. These
observations concern that source and deployment, not a universal optimum.

The first library/test build admitted 16 frontends, each with `-j2 -M4096`,
under a 96-GiB aggregate RSS watchdog. It attempted 2027 compiler invocations
in 1441.75 seconds, averaging about 15 cgroup CPU cores and peaking at
41.3 GiB aggregate RSS. Nine modules reached their individual memory limit;
the requested whole-library targets therefore failed despite extensive valid
partial progress. A 4-GiB frontend limit is not a suitable blanket assumption
for this library. Successful outputs were retained.

Source-identical focused retries passed with larger limits:

- `Modules.QuasiCoherent.Affine.Morphisms` passed with `-j8 -M20480` in
  62.97 seconds, at 5.09 GiB peak group RSS.
- `MayerVietoris.Geometric`, `BaseChange.Modules.Naturality` and
  `Restriction.Open` passed together in 127.96 seconds under the same frontend
  profile. The low-budget run's companion kernel type-mismatch diagnostic in
  Mayer--Vietoris disappeared.
- `ProjectiveSpace.Differentials.Euler.MiddleFrame` and
  `Godement.TotalComplex.QuasiIso` passed together in 221.78 seconds under
  that profile. The earlier MiddleFrame type-mismatch diagnostic also disappeared.
- `Projective.HilbertPolynomial.EulerCharacteristic`,
  `Duality.Projective.Derived.Coefficients` and
  `Projective.TwistCohomology.Coefficients` passed together with `-j4 -M24576`
  in 522.04 seconds, at 16.03 GiB peak group RSS. Their reported module times
  were 179, 303 and 518 seconds respectively.

A continuation with ten frontends at `-j3 -M8192` completed another 155
production/test modules but found six further frontend memory failures.
Focused retries at `-j4 -M24576`, with at most three concurrent frontends,
passed all six unchanged: `Restriction.Coefficients` and `Godement.Section.Units`
in 133.00 seconds; the two canonical local-model modules, `Godement.OpenBaseChange`
and `DifferentialTrace.Restriction` in 657.19 seconds. The latter batch peaked
at 20.28 GiB aggregate RSS and averaged 2.25 cgroup CPU cores. Most of its tail
was one remaining compiler, not a shortage of available worker slots.

The subsequent library continuation retained the library's CI frontend budget
(`-j4 -M12800`) and admitted seven frontends under the 96-GiB aggregate cutoff.
Keep that per-frontend baseline when widening the pool; do not trade a known
working compiler budget for speculative concurrency. Heavy exceptions can be
retried separately without invalidating successful dependency outputs.
This continuation was stopped at the user's request after 1170.10 seconds,
with 107 new production and seven new test modules completed. Its peak was
29.58 GiB group RSS with seven frontends; average cgroup CPU use was 5.18 cores.
The requested stop returned exit 143 with its process group closed. Those
successful outputs were preserved; the whole-library targets remain incomplete.

No proof, statement, heartbeat setting or package option changed between these
attempts. Native thread counts did change, so these are successful resource
configurations rather than a controlled attribution to one parameter. A kernel
type diagnostic following a memory exception warrants a well-budgeted rerun
before changing accepted source. Continue missing consumers incrementally after
the actual failures are repaired; do not discard compatible outputs.

RSS sums also need careful interpretation. A sampled Lean process included
about 1.2--1.3 GiB of file-backed resident pages, much of it shared with other
frontends. The sampled container reported about 6.2 GiB anonymous memory and
10.3 GiB file cache. Per-process RSS sums count shared pages repeatedly;
individual `-M` settings are limits, not preallocated physical memory.

The last coefficient module remained on approximately one CPU after the other
two finished. Its source-level follow-up targets are
`twistingDerivedGlobalSectionsTensorCoefficientsIso_naturality`,
`twistingFiniteCechHomologyZeroSectionsIso_hom_augmentation` and
`twistingCechIntTensorCoefficientsMap_f_zero`. Their concrete conversion
boundaries, file-wide backward-defeq settings and implicit simplifier equality
proofs are diagnostic candidates, not measured causes. The last declaration
only transports an extension-by-zero component, so derived categories alone
cannot explain all three sites. Use the focused procedure above to locate the
named task during the next otherwise-needed native compilation. A narrowly
explicit equality or abstract component calculation needs successful ordinary
compilation of the affected producer and actual consumers before adoption.
Keep separate profiling or controlled comparisons to an explicitly requested
performance investigation; they are not another acceptance chain.


