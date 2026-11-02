# Ordinary normal stages of a supported normalized chain

Source: [OrdinaryStages.lean](OrdinaryStages.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.OrdinaryStages`.
The namespace is `AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain`.

`ordinaryDatum_normalStalks_and_normalizationMap_isIso` works on the SAME
actual proper normalized-point chain `c : Z -> X`. The integral locally
Noetherian normal `X` has dimension at most two. The original total map is
an isomorphism off one actual closed nongeneric `x`, and the ONE original
stalk `S = X.stalk x` is Nagata of dimension exactly two and genuinely
satisfies `NormalModificationH1Vanishing S`.

For each native step index it derives normality of the WHOLE original
ordinary blowup `(c.ordinaryDatum j).Y`, then `IsIso (c.normalizationMap j)`.
The normalization arrow retains exactly the native endpoint equality
transport from `Stages`; no different ordinary or normalized model is chosen.

The proof has three genuine geometric cases:

- Above `x`, a dimension-two centre is rational and Nagata by the accepted
  original model-localization consumer. Its original ordinary point blowup
  is normal by the existing rational-point normality theorem.
- A lower-dimensional centre has an actual ordinary birational isomorphism
  neighborhood by normality and the coheight-at-most-one theorem. Together
  with the native away isomorphism, target-locality makes the whole ordinary
  blowdown an isomorphism and transports original normal stalks.
- A centre outside the original support lies in the original prefix's
  unchanged open. The step-prefix triangle and native restriction-composition
  law make the actual normalized step an isomorphism there. Its inverse,
  the genuinely dense nonempty source open, and the LITERAL normalization
  define a dominant section of the ordinary blowdown. The native dominant-
  section theorem gives its isomorphism on that open; the same two-open
  locality argument gives the whole ordinary blowdown isomorphism.

Normality is never assumed on the ordinary source. No rationality is required
away from `x`. Nagata, dimension and rationality are not imposed on later
stalks: they are derived exactly where used. Once the ordinary scheme is
normal, native generic-normalization isomorphism applies to that very scheme.
No finite-over-initial-base or child-completeness hypothesis occurs.

This leaf proves no singular-ancestor, canonical generation, Gorenstein,
regular-terminal or final resolution claim. The regular-point helper and
actual singular-trajectory induction remain separate consumers.

## Single classification with retained isomorphism branches

`ordinaryDatum_classification` has the SAME genuine original chain/support
inputs and returns the old normality/literal-normalization-iso pair together
with the actual ordinary blowdown isomorphism when its centre lies off the
original support or has original stalk dimension at most one. The same
three-case proof now retains the isomorphisms it already constructed. In
the over-support dimension-two branch the extra guarded conclusion is
vacuous; no centre rationality or blowdown iso is newly assumed.

The old public `ordinaryDatum_normalStalks_and_normalizationMap_isIso` keeps
its full signature and is a thin projection.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/SingularAncestors](SingularAncestors.md), [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/StepDerivedUnit](StepDerivedUnit.md).
