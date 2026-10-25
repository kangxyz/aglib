> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#original-represented-étale-cohomology-normalize-complete-values-before-specialization) · [Context](original-context.md) · [Case index](README.md) · [Previous record](transport-section-equivalences-before-specializing-the-qc-pseudofunctor.md) · [Next record](small-étale-morphism-property-boundaries-preserve-typed-native-objects.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Original represented étale cohomology: normalize complete values before specialization

The initial `Stalk/OriginalCohomologyZero.lean` proof expanded the concrete
Ext-to-native-derived comparison inside the scheme sheaf category and hit the
unchanged 200000-heartbeat limit at `whnf` (native compilation graph005).
The first unit calculation also needed an explicit unfolding of only
`rightDerivedNatIso` so its hom matched the existing native transformation lemma.

The successful repair retained exactly the original Ext.mk₀ class, native
injective resolution, represented-section isomorphism, and degree-zero derived
unit. A private abstract `representedExtZero_of_eq` takes the complete additive
comparison E, original input class x, and output value y, together with their
canonical equations. It performs the Ext.mk₀ rewrite abstractly. The concrete
scheme theorem supplies the actual objects and maps with rfl witnesses instead
of asking the elaborator to reconstruct and normalize the full sheaf carriers.

Graph007 compiled the entire changed `OriginalCohomologyZero` leaf in 28 seconds.
No heartbeat limit increase, separate test, or kernel replay was used. The
accepted `OriginalCohomology` and `ResolutionPresheaf` providers were unchanged.
This is evidence for the degree-zero normalization repair, not acceptance of
unrelated site restriction naturality or the full higher-image stalk theorem.

