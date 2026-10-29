# Intrinsic slice comparison: share the native equation before specialization

A concrete counit comparison timed out in the v4 slice presentation. The v6
repair keeps the actual native `Iso.compInverseIso` construction, proves the
whole counit equation over variable categories, and specializes that same proved
equation at the selected slice equivalence. At the product boundary, an explicit
identity-on-original-section-values equivalence bridges to the existing chosen
product fibre, preserving its second-projection formula and avoiding reduction
across implicit `getLimitCone` carriers.

The v6 `SlicePresentation` frontend and its actual `Slice.Grothendieck` consumer
compiled successfully with the existing Lean 4.34.1 and resource profile. The
153-second failed frontend and 14-second passing frontend belong to commands
with different target sets and coupled source changes; they do not establish a matched speedup or an
isolated compiler cause. Peak RSS is whole-group data, not per-file profiling.

See the [complete case record](cases/etale-slice/case.md) for exact source hashes,
bounded dependency capsules, original full-manifest locators and hashes, run
receipts, diagnostics, the preserved v4 source, and remaining boundaries.
