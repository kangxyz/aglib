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

[Representability](Representability.lean) identifies the functor of points of
`schemeOver R k n` on affine schemes over `Spec R` with Mathlib's functor (Nitsure,
arXiv:math/0504590v1, §1, pp. 7–8; Stacks, Tag 089T):

- `representableEquiv R k n A : (affineOver A ⟶ schemeOver R k n) ≃ G(k, A ⊗[R] (Fin n → R); A)`
  for `A : CommAlgCat R`, where `affineOver A = (algSpec R).obj (op A)`;
- `representableIso R k n : (algSpec R).rightOp ⋙ yoneda.obj (schemeOver R k n) ≅
  Module.Grassmannian.functor k`, a natural isomorphism of functors on `CommAlgCat R`.

The inverse `pointHom N` glues the chart maps of `N` over basic opens of `Spec A` on which `N`
lies in a coordinate chart; `homPoint g` glues the chart points of `g` by Zariski gluing for
Mathlib's functor. The focused test
[Representability](../../../AglibTest/AlgebraicGeometry/Grassmannian/Representability.lean)
restates both with the instance from `BaseChangeFormula` and guards their axioms.

[FunctorOfPoints](FunctorOfPoints.lean) treats nonaffine test schemes. For `T` over `Spec R`,
`algSpecPoints T := (algSpec R).rightOp ⋙ yoneda.obj T` is its functor of points on
`R`-algebras, and:

- `algSpecPointsEquiv T X : (T ⟶ X) ≃ (algSpecPoints T ⟶ algSpecPoints X)` for all `T`, `X`
  over `Spec R` (maps glue along the affine open cover of `T`). This part is not specific to the
  Grassmannian;
- `Grassmannian.homEquivNatTrans k n T : (T ⟶ schemeOver R k n) ≃
  (algSpecPoints T ⟶ Module.Grassmannian.functor k)`, natural in `T`
  (`homEquivNatTrans_comp`);
- `Grassmannian.localFunctor R k n : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1)`,
  `T ↦ (algSpecPoints T ⟶ Module.Grassmannian.functor k)`, the extension of Mathlib's functor
  to all schemes over `Spec R` by natural transformations from the affine functor of points (a
  right Kan extension along `algSpec`). It is represented by the Grassmannian:
  `Grassmannian.localFunctorRepresentableBy R k n :
  (localFunctor R k n).RepresentableBy (schemeOver R k n)`. Equivalently,
  `Grassmannian.localFunctorIso R k n : yoneda.obj (schemeOver R k n) ⋙ uliftFunctor ≅
  localFunctor R k n`: `yoneda.obj` lands in `Type u` and `localFunctor` in `Type (u + 1)`, so
  this comparison uses `uliftFunctor`, while Mathlib's `RepresentableBy` allows the larger value
  universe.

The description of maps `T ⟶ schemeOver R k n` as rank-`k` locally free quotients of
`O_T ⊗ R^n` (Stacks, Tag 089T) needs sheaves of modules and is not yet proved.

Relocation candidates (general, not specific to the Grassmannian): `algSpecPoints`,
`algSpecPointsEquiv` and `AlgebraicGeometry.AlgSpecPoints.*` in
[FunctorOfPoints](FunctorOfPoints.lean), and `Grassmannian.locAway` and
`Grassmannian.span_range_eq_top_of_forall_notMem` in [Representability](Representability.lean),
belong to a lower owner for schemes over `Spec R`. After such a move, `exists_chartLocal` can be
derived from `AlgSpecPoints.exists_locAway_comp_eq`.
