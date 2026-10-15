# Section rigidity for formally unramified morphisms

[SectionRigidity](SectionRigidity.lean) gives
`AlgebraicGeometry.Scheme.Hom.eq_of_comp_eq_of_section`. For an actual scheme
map `p : X ⟶ Y`, it retains `IsSeparated p`, `FormallyUnramified p` and
`LocallyOfFiniteType p`. Given a geometrically connected `q : Z ⟶ T`, a
specified section `s : T ⟶ Z` with `s ≫ q = 𝟙 T`, and maps `f g : Z ⟶ X`,
the equations `f ≫ p = g ≫ p` and `s ≫ f = s ≫ g` imply `f = g` as actual
scheme morphisms.

The equalizer is the pullback of the diagonal of `p`. Its inclusion is both
open and closed. The section meets it in every connected fibre of `q`, so
the inclusion is surjective, hence an isomorphism. The proof keeps these
actual maps. Neither the source/parameter nor the base requires a field,
Noetherianity or reducedness assumption; `p` is not assumed finite or etale.

Focused imports are Mathlib's formally unramified and separated morphisms,
geometric connectedness, the surjective-open-immersion isomorphism criterion
and connected clopen subsets. This leaf does not depend on the finite-etale
category or a pointed model. The original R5 pointed all-test-object adapter
remains downstream and consumes this general theorem. The isolated
`AglibTest.UnramifiedRigidity` client checks the same weak premises and full
scheme-map equations.
