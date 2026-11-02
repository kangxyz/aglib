# Conditional original exceptional inverse line

Source: [PointBlowupInverseLine.lean](PointBlowupInverseLine.lean).

Import:
`Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.PointBlowupInverseLine`.

`normalSurfacePointBlowupExceptionalCanonicalInverseLineIso` constructs

```
Ω(E, jE, derivedResidueCoefficientLine R κ(x)) ≅ (exceptionalLine S hdS)∨
```

for the actual full exceptional scheme of the original parent stalk
`S = P.presheaf.stalk x`. The projective embedding `jE`, its finite index
equivalence and positive index bound, and its original structural triangle
are supplied once and used in the existing localized Cartier isomorphism.
No trivialization of the original residue coefficient line is selected.

The hypotheses are exactly the original conditional frame telescope plus
that same exceptional projective presentation: genuine original global
models over `R`, original rational normal Nagata centre of dimension two,
original residue triangle, native finite self-injective dimension of the
original parent stalk, and the unchanged full exceptional generation
premise `Epi (globalSectionsEval (i*(a*ωZ)))`.

The construction first restricts the inverse of the SAME original-map
isomorphism proved in `PointBlowupFrame`. With the native pullback-unit
comparison and `localizedExceptionalCanonicalRestrictionIso`, this yields
`eTriv : Ω ⊗ L ≅ O_E`. It then uses
`lineBundleDualTensorEquivalence E L`:

1. the inverse of its counit at `Ω` inserts the original dual/line pair;
2. its functor maps the original braiding `L ⊗ Ω ≅ Ω ⊗ L` followed by
   this actual `eTriv`;
3. the original right unitor identifies `L∨ ⊗ O_E` with `L∨`.

Thus actual dual evaluation, braiding, associators and unit maps are
preserved. The canonical coefficient is not assumed invertible before
cancellation; the constructed isomorphism proves it is the specified dual.
The existing Serre dimensions and anticanonical Hilbert consumers remain
unchanged and are not reimplemented.

The full exceptional-generation premise remains explicit; the theorem
does not derive arbitrary-field generation or initial full cones.
