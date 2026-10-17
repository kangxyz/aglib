# Grassmannian schemes

This family will own the Grassmannian `Gr(E, k)` of rank-`k` locally free quotients of a finite
locally free module and the projective bundle `P(E) := Gr(E, 1)`
([Picard plan](../../../doc/PICARD_PLAN.md), rows F8 and F9). Its ring-level input is
[RingTheory/Grassmannian](../../RingTheory/Grassmannian/README.md): charts of Mathlib's
`Module.Grassmannian.functor`, their coordinate rings, overlaps, local covering, and Zariski
separatedness and gluing.

Every statement below that involves Mathlib's `Module.Grassmannian.map` assumes the named premise
`Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)` described in
[RingTheory/Grassmannian](../../RingTheory/Grassmannian/README.md); the glued scheme
`glueData`, `scheme` and `toBase` take it as an instance argument.

[Chart](Chart.lean) constructs the affine charts over `Spec R` for `R : CommRingCat` and
`x : Fin k → (Fin n → R)`:

- `chartScheme R x : Over (Spec R)` is `Spec (ChartRing R x)` with its structure map, written
  with Mathlib's `algSpec R`.
- `chartFunctor R x : (Over (Spec R))ᵒᵖ ⥤ Type u` is `(algΓ R).leftOp ⋙ (chartFunctor R x).toFunctor`:
  a scheme `T` over `Spec R` goes to the points of
  `G(k, Γ(T, ⊤) ⊗[R] (Fin n → R); Γ(T, ⊤))` in the chart at `1 ⊗ x`.
- `chartRepresentableBy R x : (chartFunctor R x).RepresentableBy (chartScheme R x)` holds on
  all of `Over (Spec R)`. It composes Mathlib's adjunction `algΓAlgSpecAdjunction R` with
  `Module.Grassmannian.chartFunctorCorepresentableBy`.

[Overlap](Overlap.lean) constructs the overlaps `chartOverlapScheme R x y`, the spectrum of
`Localization.Away (chartTransitionDet x y)`, with the open immersion
`chartOverlapToChart R x y` into the chart at `x` (`isOpenImmersion_chartOverlapToChart_left`;
an isomorphism for `y = x`, `isIso_chartOverlapToChart_self_left`),
the representation `chartOverlapRepresentableBy R x y` of
`(algΓ R).leftOp ⋙ (chartFunctor R x ⊓ chartFunctor R y).toFunctor` on all of `Over (Spec R)`,
and the transition isomorphism `chartOverlapIso R x y` with the overlap computed from `y`.

The representations use global sections, which is correct for these functors because the charts
and overlaps are affine; `Module.Grassmannian.functor` composed with global sections is not a
Zariski sheaf on nonaffine schemes and is not claimed to be represented.

This is the representability of the subfunctors `F_i` in Stacks, Tag 089T, and of their
pairwise intersections. `chartRepresentableBy_homEquiv_comp_chartOverlapToChart` and
`chartOverlapRepresentableBy_homEquiv_comp_chartOverlapIso` show that the inclusions and the
transition isomorphisms preserve the classified point.

[Gluing](Gluing.lean) constructs Mathlib's `Scheme.GlueData` `glueData R k n` over the
coordinate tuples `ULift (Fin k → Fin n)`: charts `chartScheme`, overlaps `chartOverlapScheme`,
transitions `chartOverlapIso`, and the triple-overlap maps `tripleT`. Every gluing identity holds
because the maps preserve the classified point (`tripleT_fac`, `tripleTOver_cocycle`). The glued
scheme `scheme R k n` has the structure morphism `toBase R k n` (`ι_toBase`) and is
`schemeOver R k n` over `Spec R`. For maps `a`, `b` from a scheme over `Spec R` into two charts,
`a ≫ chartι I = b ≫ chartι J` holds exactly when `a` and `b` classify the same point of
`Module.Grassmannian.functor` (`comp_chartι_eq_of_point_eq`, `point_eq_of_comp_chartι_eq`).

Consequently `chartLocalEquiv T`, for every scheme `T` over `Spec R`, identifies the maps
`T ⟶ schemeOver R k n` that factor through a coordinate chart (`ChartLocalHom`) with the points
of `G(k, Γ(T, ⊤) ⊗[R] R^n; Γ(T, ⊤))` that lie in a coordinate chart (`ChartLocalPoint`).

The identification of the whole functor of points of `scheme R k n` with
`Module.Grassmannian.functor` on `R`-algebras (gluing over a cover of `Spec A`), and its
sheaf-level description on `Over (Spec R)`, are not yet proved.
