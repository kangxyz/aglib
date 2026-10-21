# The actual fibre ideal over a discrete valuation ring

`Aglib.AlgebraicGeometry.IdealSheaf.Cartier.DVRFibre` proves the existing
`Scheme.Hom.Cartier.FlatDVRFibreIdealTrivial` family, with all its original
quantifiers. For any commutative domain `R` in universe `u` with
`IsDiscreteValuationRing R`, any `X : Scheme.{u}`, and any flat
`π : X ⟶ Spec (.of R)`, it constructs

```lean
idealModule
  (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≅
    SheafOfModules.unit X.ringCatSheaf
```

The module and the fibre projection are exactly those in
[`Cartier.Interfaces`](Interfaces.lean). Flatness is the only geometric
assumption: there is no regularity, Noetherianity, properness, elliptic-curve,
reduced-fibre, or component hypothesis, and no trivialization or theorem-family
supplier is an input.

`dvrResidueKernelBasis` chooses a singleton basis of the actual nonzero
principal ideal `ker (IsLocalRing.residue R)`. This kernel equals the maximal
ideal. `dvrResidueIdealIso` sheafifies that basis through `affineIdealIso` and
the existing tilde/free comparison. The choice is the ordinary choice of a
generator of the actual maximal ideal of a DVR.

`flatDVRFibreIdealBaseChangeIso` uses the canonical `idealPullbackMap` on the
flipped literal pullback square for `π` and the original residue-field
immersion. Its invertibility follows from
[`BaseChange.FlatMorphism`](../BaseChange/FlatMorphism.lean), since the residue
immersion is affine and `π` is flat. The equation
`flatDVRFibreIdealBaseChangeIso_hom_inclusion` retains the actual ideal
inclusions and the canonical pullback-unit map. Finally,
`flatDVRFibreIdealIso` composes the inverse comparison with the pullback of
`dvrResidueIdealIso` and the canonical unit isomorphism.

`flatDVRFibreIdealTrivial` is the genuine inhabitant of the existing family;
the preceding isomorphisms also provide pointwise constructions. The proof is
authored against Aglib HEAD `3a4d549981ced306d89d3ed55418c9e6a25f86c4`, Lean
4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. It is a direct
formal derivation from native definitions and the cited lower APIs. Source
attributions in the older interface are not used as mathematical premises.
Native evidence is returned separately for the actual source hashes.
