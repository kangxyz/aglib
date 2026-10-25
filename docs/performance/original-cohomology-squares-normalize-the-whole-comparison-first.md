> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#original-cohomology-squares-normalize-the-whole-comparison-first) · [Context](original-context.md) · [Case index](README.md) · [Previous record](finite-pointed-lifts-name-the-residue-point-morphism.md) · [Next record](chart-ext-comparisons-abstract-the-complete-values-before-specialization.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Original cohomology squares: normalize the whole comparison first

CohomologySquare graphs079 and082 timed out during ordinary compilation
when reducing inverseImageSquareIso at concrete components. Normalize the
whole isomorphism chain first using the generic iso_comparison_square and
the native inverseImageSquareIso_comp_hom equation. Then use congr_app and
an additive element-transport lemma with explicit AddCommGrpCat.comp_apply
and typed Eq.trans, rather than unfolding the original sheaf carriers.
Graph084 accepted SquareComparison in2.7 seconds; graph085 accepted
SquareTransport in885 milliseconds and CohomologySquare in16 seconds.
The original maps and four independent Ext universes are retained, without
new mathematical premises, larger budgets, or additional replay/benchmarks.

