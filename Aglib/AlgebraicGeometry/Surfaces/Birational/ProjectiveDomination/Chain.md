# Literal pullbacks of original point-blowup chains

Import `Aglib.AlgebraicGeometry.Surfaces.Birational.ProjectiveDomination.Chain`.

For an actual `BlowupDatum I` on `X`, an original map `g : Y → B.Y`, and
`π : W → X`, `BlowupDatum.chainPullbackIso` constructs the canonical
isomorphism

```text
pullback (g ≫ B.map) π ≅ pullback g (pullback.fst B.map π).
```

It is the inverse of Mathlib's `pullbackRightPullbackFstIso`. The categorical
comparison requires no hypotheses on a centre. In a cons case of the actual
`PointBlowupChain`, its datum is exactly
`B = blowupDatum (X.fromSpecResidueField x).ker`; the original closed point,
its closedness proof, its local dimension-two proof, and the original tail
remain the constructor's data.

`chainPullbackStepMap` is the canonical map from the left pullback to
`pullback B.map π`. Its first projection is `pullback.fst ≫ g`, and its
second projection is the original `pullback.snd`. The isomorphism's
`_hom_fst` and `_hom_snd` equations retain the complete projections to `Y`
and to this literal first pulled-back step. The `_hom_snd_fst` and
`_hom_snd_snd` equations give their original components. The `_inv_fst`,
`_inv_snd`, and `_inv_stepMap` equations retain the projections in the
opposite direction.

`chainPullbackStepMap_triangle` and `chainPullbackIso_hom_triangle` retain
the original structural maps to `X`. For every original `s : W → S`,
`chainPullbackIso_hom_structure` proves that the composite structural map
through the nested pullback is exactly `pullback.snd (g ≫ B.map) π ≫ s`.
For the structural map of a projective embedding, take
`s = j ≫ ProjectiveSpace.toSpec A κ`.

`PointBlowupChain.isLocallyNoetherian` proves

```text
PointBlowupChain f → IsLocallyNoetherian X → IsLocallyNoetherian Y
```

for the original chain map `f : Y → X`. The induction applies the existing
`BlowupDatum.isLocallyNoetherian` supplier from
`Surfaces/Resolution/WeakTransform.lean` to each original point blowup,
then passes that actual source as the base of the original tail. It does
not impose Noetherianity on arbitrary base changes, nor replace those
base changes by blowups of image ideals.

This checkpoint retains only the categorical pullback, projection and
original-Noetherianity interfaces above. The uncompiled forward projective
embedding induction and its `ProjectivePresentation.Embedding` import are
excluded. No forward embedding or full contraction closure is claimed.

No exact byte backup was present in the author's scratch. The Lean file was
reconstructed from frozen production source
`82180ada3455d56dd909a3313a59050f43f31c5fb4cd4b43ebf384c1833f46ef`
by removing only that forward-specific import, its two-line module description,
and the private induction helper plus public forward embedding theorem; the
module title was restored. Its resulting SHA256 is
`f6df6589aad097fd20516b460e2c8d100a3226e6ca3ab207867af0306d28dc09`,
exactly matching the previously passed completed-only source. That source
passed ordinary native compilation in `afc4725e`, source `f7f8f219`, in
6.1 seconds at standard budgets. This retains exact-source coverage, not a
fresh compiler pass on the final checkpoint dependency graph. Root owns the
single normal final checkpoint batch.

The pair is prepared only under the author's `checkpoint-chain` scratch
directory. Production P and latest-main R remain unchanged. No new proof,
build, test, probe, replay, or Git operation was performed. The original
source basis is Aglib HEAD
`8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean 4.34.1.
