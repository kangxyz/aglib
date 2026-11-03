# The same local image and the own terminal canonical stalk

Source: [LocalImageFrame.lean](LocalImageFrame.lean).

`normalSurfaceCanonicalLocalImage_stalkFrame_of_pullback_surjective` is a
conditional pointwise comparison, not a canonical-generation producer.
It retains the original regular-local-domain base and the actual global
normal integral surface embeddings of X and Z, their separate coordinate
data, dimensions and finite generic-image maps, and the original proper
structural triangle f:Z→X.

The actual square `IsPullback a p f (X.fromSpecStalk x)` retains the SAME
integral local model T, with dominant p. The own canonical module on Z is
pulled back along a; no canonical object on arbitrary T is chosen. The
image line is the SAME comap of the SAME original canonical numerator.
Its local rank-one property is explicit and is supplied by actual ideal
principalization, not assumed for the canonical target.

Two genuine producer inputs remain explicit:

* the original `moduleDerivedPushforwardUnit X f` is an isomorphism;
* the actual stalk map of the original inverse-trace pullback, transported
  through `pullbackTriangleIso` for the SAME square, is surjective.

The former yields the actual trace isomorphism by the existing theorem.
Neither input follows from image rank one. Supported-unit geometry and
singular-trajectory exceptional generation must discharge them upstream.

The actual localization projection's stalk map is an isomorphism. The native
extension/restriction unit and `pullbackModuleStalkIso` transfer the OWN
canonical target's proved torsion-freeness and nontriviality. They are not
extra assumptions. Native `TorsionQuotient` then identifies the actual image
stalk with this target, retaining the exact equation `E.comp q_t = v_t`.
The final own canonical frame uses the SAME original scalar isomorphism
and native `ModuleCat.restrictScalarsIsoOfEquiv`.

The point t is over the original closed point of O_X,x. The theorem derives
`f (a t) = x`; no conclusion is made about untouched singularities off x.
No new denominator, generic frame, fraction field, tensor model, target-rank
premise, finite-parent-map premise or Gorenstein criterion is introduced.
The existing own canonical stalk criterion remains the later consumer.
