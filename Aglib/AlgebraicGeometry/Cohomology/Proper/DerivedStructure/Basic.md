# Original structural derived units and native H0

For a scheme `X` and the actual ring map `α : R → Γ(X,O_X)`,
`moduleStructuralSectionsMap` is the original map `r ↦ α(r)` on the
whole-space section carrier. `moduleDerivedStructure` is the installed
bounded-below right-derived global-sections object of the original
structure module. `moduleDerivedStructureUnit` is the single of that
section map followed by the existing `rightDerivedSingleUnit`.

`moduleDerivedStructureUnit_homology` and its evaluation theorem identify
the same native H0 arrow with the original structural section map, through
the existing single and left-exact R0 comparisons. Bijectivity of `α`
therefore makes that H0 arrow invertible. Global sections retains its
original finite-limit hypothesis and is not assumed exact.

For an arbitrary scheme morphism `g : Y → X`,
`moduleDerivedPushforwardUnit` is the single of the literal structure-module
coefficient arrow followed by the installed derived pushforward single
unit. Its map and arguments are unchanged.

This owner imports the original section functor and native single/H0
comparison. `Proper/DerivedStructure` imports it and retains the old
`Sheaf.H` normalization, nonnegative and surface upper bounds, Postnikov
and Leray constructions, and original H1 map comparison.
