# Scheme Cech comparison: one scoped cost diagnostic

The requested diagnostic is complete. The passed source was preserved byte-for-byte: Scheme `Cech/Comparison.lean` SHA `a9ff484188f60dc58dfe142249bc28ed0cf9fbde1280020dba63d2c5b9a76e8a`. One frontend succeeded with the normal pins, default budgets and resource profile; no production source changed and no second profile ran. The nine-file implementation remains separately compiled and reviewed.

The native `setup-file --no-build` preparation started no compiler. Its reconstructed setup has SHA `1f0adc79ba795e65b54db2f53e679690f57b51a999495f3ededacfb42099a159`; the removed original setup's byte identity is not claimed. The diagnostic used `trace.profiler=true` with a 100 ms display threshold. It took 641.305 seconds, produced 66,793,397 bytes of trace, and reached a 2,355,453,952-byte native owned-tree RSS peak. This is an instrumented observation, not a matched benchmark against the earlier 155-second ordinary pass.

The largest named kernel intervals were concentrated in cohomology adapters and scalar specializations, despite their short source bodies. Source lines below refer to the frozen `source.lean` supplied with the diagnostic; trace lines refer to the full retained stdout.

| Declaration | Source line | Kernel interval | Trace line |
| --- | ---: | ---: | ---: |
| `moduleHPrimeTopAddEquiv_scalar` | 249 | 16.698 s | 91094 |
| `sheafHPrimeTopAddEquiv` | 96 | 16.485 s | 54622 |
| `module_additiveResolutionHomologyEquiv_scalar` | 428 | 15.259 s | 151177 |
| `resolutionSectionShortHomologyEquiv` | 410 | 13.340 s | 144888 |
| `additiveResolutionHomologyEquiv` | 298 | 13.131 s | 118033 |
| `moduleCechCohomologyAddEquiv_scalar` | 740 | 11.661 s | 216969 |

Other substantial kernel intervals were the canonical module comparison (10.734 s), its supplied-resolution view (10.224 s), equality-to-canonical (10.108 s), and resolution independence (9.970 s). These are individual inclusive intervals; they are not summed or converted into wall-time percentages.

Elaboration has a different visible hotspot: `subsingleton_sheafHPrime_of_moduleResolution_sections_exact` took 36.434 s in its value frame, and `geometricCechRowAugmentation_naturality` took 23.258 s. The open-kernel section-surjectivity value frame took 13.849 s. Repeated `sectionsFunctor`/`G.PreservesZeroMorphisms` searches took 5.045, 5.028 and 5.011 s (trace lines 67127, 65850, 66384). Inside the same resolution argument, trace lines 71175–71220 show the actual full-subcategory zero dictionary being compared with the preadditive zero dictionary; one nested comparison is about 2.33 s.

A bounded existing-proof repair is justified at that dictionary boundary. The first useful attempt is to supply the already proved preservation witnesses at the literal Scheme/module and additive-sheaf category/zero heads, in the smallest local scope covering both theorem headers and bodies of `moduleResolution_openKernelSections_surjective` and `subsingleton_sheafHPrime_of_moduleResolution_sections_exact`. The actual `sectionsFunctor` is already `SheafOfModules.additiveEvaluation`; the precise arbitrary-zero preservation API and validated method exist in `Algebra/Category/ModuleCat/Sheaf/Evaluation.lean` and `docs/performance/native-evaluation-zero-dictionaries.md`. This needs no new hypothesis, functor, model, global priority or budget.

The kernel-heavy AddEquiv boundary warrants a separate small pilot, not a blanket rewrite. Trace lines 142–174 compare the Scheme carrier presentation with `X.toTopCat`; nested frames at 179–1130 descend through Ext's additive structure, `Ext.homEquiv`, `Localization.SmallHom.equiv` and `equivShrink`. This supports inspecting a single native site/Ext/group presentation around `sheafHPrimeTopAddEquiv` and its actual scalar consumer. Keeping the whole generic comparison head may help; blindly omitting result types or switching every `def`/`abbrev` could merely move work downstream. The profile does not establish which kernel conversion is causal, or that a proposed presentation change will improve total cost.

No adequately labelled import or serialization breakdown was visible. Large enclosing command or asynchronous frames may include waits for kernel tasks. Overlapping frames and the instrumented measurement prevent allocating the earlier 155 seconds precisely; the cost of producing the large trace was not separately measured. A source-preserving repair and ordinary changed-input validation are a next step, not an achieved speedup or an outstanding mathematical proof.

Exact runtime/setup/source metadata, sorted frames, evidence links and the repair judgment are in `result.json`. Full raw evidence remains in the broker's `migration/incremental-compiler/diagnostics/cech-profile-6536a791/` package, with native receipt/run `6536a79189ea41d098aedfdb4272f3a9`. Reproduce only the analysis with `python3 analyze.py`; this does not invoke Lean or request another profile.
