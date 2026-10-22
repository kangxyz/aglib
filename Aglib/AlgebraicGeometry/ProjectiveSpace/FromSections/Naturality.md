# Source naturality of projective morphisms from sections

`Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality` retains the
original coordinate type `I` under an arbitrary scheme morphism `g : T ⟶ X`.
For the original section maps `s i : 𝟙_X ⟶ M`, its actual family is

```text
pulledFamily g s i = (pullbackUnitIso g).inv ≫ (Modules.pullback g).map (s i).
```

`pulledFamily_desc` identifies its original free map with the pulled free map
through `pullbackFreeIso g I`. Thus `pulledFamily_epi` derives generation from
`Epi (Sigma.desc s)`. No new generation premise, flatness, or change of index is
introduced. `pullbackSection_global` identifies each literal section map with
the original geometric pullback-adjunction unit on global sections.

`mapOfFiniteFamily_pullback` proves the actual equality

```text
g ≫ mapOfFiniteFamily p M hM s =
  mapOfFiniteFamily (g ≫ p) ((Modules.pullback g).obj M)
    (pullback_locallyRankOne g M hM) (pulledFamily g s).
```

For an actual module isomorphism `e : g*M ≅ N`,
`mapOfFiniteFamily_pullback_iso` derives the rank-one and generation witnesses
for `N` and uses the same original section maps followed by `e.hom`.
`mapOfFiniteFamily_iso` also compares any two displayed original families under
an actual section-preserving module isomorphism. Their exact section equations
are its input; no desired morphism equality is an input.

The proof constructs the pulled original frames on the actual inverse-image
opens by recovering the original frame cocycle and pulling its genuine
generators. `SectionFrames.pullback_coefficientOn` identifies each new
coefficient with `g.appLE` of the corresponding original coefficient.
`pullback_chartRingHom` then identifies the literal projective chart ring maps,
and `pullback_map` proves equality on this full pulled frame cover. Independence
of frame choice follows from actual generator ratios on common opens and the
native projective chart overlap theorem.

The assumptions are an arbitrary commutative coefficient ring, arbitrary
schemes and scheme morphism, an actual locally rank-one module, and a finite
original generating family. There is no field, reducedness, Noetherian,
coherence, nontriviality or flatness premise. The empty-scheme and empty-index
cases are retained whenever the original generation hypothesis holds.
