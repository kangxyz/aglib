# The unique lift of the original trait section

`Scheme.ProperTraitSections.existsUnique_lift R F p f s hs` takes the
original DVR `R`, its specified fraction field `F` and algebra map,
`p : X ⟶ Spec R`, a proper morphism `f : Y ⟶ X`, the original section
`s : Spec R ⟶ X` with `hs : s ≫ p = 𝟙 _`, and `IsIso` of the original map

```lean
(Over.pullback (baseMap R F)).map
  (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)
```

It proves `∃! t : Spec R ⟶ Y, t ≫ f = s`. Properness of `p` is not
assumed. Neither model is required to be regular, integral, flat or
excellent. There is no given lift or alternate-section premise.

The chosen `lift` retains the exact original equations:

- `lift_comp`: its composite with `f` is the original `s`.
- `lift_toBase`: it is a section of the original composite `f ≫ p`.
- `lift_generic`: restriction along the original fraction-field spectrum
  map is `genericLift`, defined using the inverse of that same native
  generic-fibre map.
- `lift_genericSection` and `lift_genericSection_comp`: its literal native
  generic section equals the inverse transport of the original generic
  section, and the forward map returns that original section.
- `lift_unique`: every map whose composite with `f` is `s` is this lift.

The generic sections are the existing
`Scheme.GenericSection.genericSection`, on the original categorical
pullbacks. Their functoriality shows that every possible section lift has
the same prescribed generic restriction. The inverse of the actual native
generic map constructs a map `Spec F ⟶ Y` with the original triangle over
`X`. This defines a native `ValuativeCommSq f` with exactly `R`, `F` and
`s`. The native proper valuative criterion supplies its unique lift.
Since every map over `s` has the same generic restriction, the uniqueness
applies to all original section lifts, not just a selected generic fibre.
No new valuation ring, model, or generic-fibre structure is introduced.

This general Proper owner has no surface import. For an actual
`PointBlowupChain` over a proper DVR model, the existing chain properness
and `PointBlowupChain.genericBaseChange_isIso` supply the two morphism hypotheses.
That small surface corollary belongs to a later surface consumer and is
not added upward here or to the frozen Trait file.

Original basis: HEAD `3a4d549981ced306d89d3ed55418c9e6a25f86c4`, with live
overlay. The exact existing sources read were
`Proper/GenericExtension.lean` at
`ab6b4efb6aede54825396dc316aed860a350a0e15bba7297a9fe90440a33cec5`
and `Stalk/GenericSection.lean` at
`d02b4334b14a1d858c5d7d32071021ff7e180e8a1d1e99d815f2f16e5b914d3a`.
Only this new pair is written. The complete Lean source
`68a6775966db9b528d5d6822faa696ca93838f6c50116f69113c6840c05539ce`
passed its native leaf in 4.1 seconds in
`remote-e63e4b1c42174e9899be14c21e70c3f8`, SOURCE
`8181b9f19b209ae2468a22987fc7b7472b54dc1b653991a112576d33b27a5973`.
The whole incremental graph succeeded, with one fresh frontend and the
unchanged suppliers reused. The default 200000-heartbeat budget remained
in force. The exact passed pair and evidence are preserved separately from
this doc-only status correction; the Lean bytes remain unchanged.
Native success does not replace independent mathematical review.

The supplied `IsFractionRing R F` and original generic-map `IsIso`
hypotheses are explicitly retained in the existence theorem. This is
conditional section lifting through that actual proper morphism, not an
unconditional lifting statement for arbitrary proper maps. Resolution,
common-model construction and minimality are separate consumers.
