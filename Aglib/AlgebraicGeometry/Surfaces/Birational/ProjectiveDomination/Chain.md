# Literal pullbacks and finite embeddings of original point-blowup chains

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
The projective-embedding induction uses
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

`PointBlowupChain.exists_projective_embedding_pullback c π j` takes an
original `c : PointBlowupChain β` for `β : Y → X`, a locally Noetherian
original `X`, an arbitrary `π : W → X`, and a closed immersion
`j : W → ProjectiveSpace A κ` with `Finite κ`. It constructs

```text
∃ (J : Type u) (_ : Finite J)
  (k : pullback β π → ProjectiveSpace A J),
  IsClosedImmersion k ∧
    k ≫ ProjectiveSpace.toSpec A J =
      pullback.snd β π ≫ j ≫ ProjectiveSpace.toSpec A κ.
```

The identity case uses the original pullback projection followed by `j`.
The cons case invokes the concrete
`ProjectivePresentation.exists_projective_embedding B π j`, recurses on
the original tail over `pullback B.map π`, and precomposes with
`chainPullbackIso`. The original structural equation follows from the
two concrete embedding equations and `chainPullbackIso_hom_structure`.
No family of projective embeddings or other conclusion-equivalent premise
is supplied to the theorem. No structural map on `X` or Noetherianity of
the arbitrary new base `W` is added.

The associativity and original-Noetherianity package previously passed at
SHA256 `f6df6589aad097fd20516b460e2c8d100a3226e6ca3ab207867af0306d28dc09`
in native run `afc4725e` (source `f7f8f219`, 6.1 seconds). The current
increment adds the forward embedding induction and its precise public
import of the concrete single-step provider. The latter source candidate,
`Blowup/ProjectivePresentation/Embedding.lean`, was reconciled at SHA256
`73f03488a80c83b2358f359ea5277a04b5551fd9219eca045e24ed0dd37abb42`.
It has the exact binder and existential order used above.

The new whole-module candidate and its single-step dependency await the
shared native compilation batch; the older pass does not cover this
increment. No local build, test, replay, or diagnostic probe was run.
The source basis is Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean 4.34.1. It uses the
standard theorem budget without additional options.
