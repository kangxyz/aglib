# The original generic fibre of a finite point-blowup chain

For the original DVR `R`, its specified fraction field `F` and algebra map,
an actual proper structural map `p : X ⟶ Spec R`, and an actual
`c : PointBlowupChain f` with `f : Y ⟶ X`, the theorem
`PointBlowupChain.genericBaseChange_isIso` proves `IsIso` of

```lean
(Over.pullback (baseMap R F)).map
  (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)
```

`PointBlowupChain.genericIso` is `asIso` of that exact arrow. Its
`genericIso_hom`, `genericIso_hom_fst` and `genericIso_hom_snd` equations
retain respectively the literal native map, the original composite with
`f`, and the original structural map to `Spec F`. The fibres are the
original category-theoretic pullbacks from the existing trait API.

The scheme `X` is not required to be regular, integral or flat. Properness
over the DVR implies local Noetherianity, which is used solely to keep
the actual intermediate blowup models proper. The chain is the existing
finite `PointBlowupChain`, including its actual closed centres and
two-dimensional stalk witnesses. No new chain or trait-graph construction
is introduced.

First, the original proper map sends a closed centre to a closed point of
the trait, hence to its unique closed point. The specified fraction-field
map takes its point to the generic point, which differs from that closed
point because a DVR is not a field. Thus the original centre's ideal pulls
back to the unit ideal on the entire literal generic fibre.

The existing `BlowupDatum.pullback_snd_isIso_of_comap_eq_top` identifies
the original pullback projection, using the native universal property of
the same blowup. Pullback pasting identifies the native `Over.pullback`
map with this isomorphism. This off-centre argument supplies the needed
comparison directly, without an additional flat-base-change family or
an abstract fibre isomorphism premise. Induction then composes the actual
generic maps of the supplied finite chain. The proof keeps compatible
structural triangles through the associativity step.

Original basis: HEAD `3a4d549981ced306d89d3ed55418c9e6a25f86c4` with live
overlay. The unchanged supplied chain owner is `Principalization.lean`
at `b203b9f0f3e0dd22585692ccc708030e7ed98252ecef57dd93450051079de48c`;
the unchanged trait owner is `TraitGraph.lean` at
`ad18f3d5e3489adf4c21524c53676ca29bb025d753d237842c95c392fb493ad5`.
This new pair is the only writable source here. The complete Lean source
`d45e00813a04377552cb2d5e39a2d7f2542db0911377f6f6fbcf8040f33de8dd`
passed its native leaf in 3.0 seconds in
`remote-e9d77432522a41bcb10448bfddd353c0`, SOURCE
`31d91a46be5a33dbf01ddb32ec703c50c947afbf473d80eef68b147c9c5696a2`.
The whole incremental graph succeeded, with one fresh frontend and the
unchanged passed suppliers reused. The default 200000-heartbeat budget
was retained. The exact passed pair and evidence are preserved separately
from this doc-only status correction; the Lean bytes remain unchanged.
Native success does not replace independent mathematical review.

The endpoint concerns preservation of the original generic fibre by a
given actual chain. It does not construct a resolution of a singular
model, a common regular domination, a contraction, or a minimal model.
