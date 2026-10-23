# Grassmannian schemes

This family will own the Grassmannian `Gr(E, k)` of rank-`k` locally free quotients of a finite
locally free module and the projective bundle `P(E) := Gr(E, 1)`
([Picard plan](../../../docs/PICARD_PLAN.md), rows F8 and F9). Its ring-level input is
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

[Quotient](Quotient/) proves the description of the Grassmannian by locally free quotients
(Stacks, Tags 089S and 089T, TeX snapshot `a04446e5`; Nitsure, arXiv:math/0504590v1, §1,
Exercises (2), p. 5). A `LocallyFreeQuotient X k n` is an epimorphism `O_X^n ⟶ Q`, with
`O_X^n = SheafOfModules.free (ULift (Fin n))` and `Q` of constant rank `k` (`SheafHasRank`);
isomorphism classes under `O_X^n` (`LocallyFreeQuotient.IsoUnder`) form
`quotFunctor R k n : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1)`, with pullback through `pullbackFreeIso`
([Basic](Quotient/Basic.lean)). Convention: `k` is the rank of the quotient, so this is Stacks'
`G(n − k, n)` and Nitsure's `Grass(n, k)`, for all `k` and `n`. On `Spec A`, such quotients are
the points of `G(k, A ⊗[R] R^n; A)`, compatibly with base change (`affinePoint_bijective`,
`affinePoint_pullback`; [Affine](Quotient/Affine.lean), [BaseChange](Quotient/BaseChange.lean),
[Points](Quotient/Points.lean)). The natural transformation
`toLocalFunctor R k n : quotFunctor R k n ⟶ localFunctor R k n` is injective on every `T`,
because local isomorphisms under the quotient maps glue
([Injectivity](Quotient/Injectivity.lean)), and surjective, because the chart quotients of a point
form a Zariski descent datum (`Pseudofunctor.DescentData.ofEpi`) and glue
([Surjectivity](Quotient/Surjectivity.lean)). Hence
`quotFunctorIso R k n : quotFunctor R k n ≅ localFunctor R k n`, and `schemeOver R k n`
represents `Quot_k(O^n)` on all schemes over `Spec R` (`quotFunctorRepresentableBy`), with
universal quotient `universalQuotient R k n` and a representative `universalQuotientRep R k n`
([Representability](Quotient/Representability.lean)); the identification of the universal
quotient with the chart quotients is not stated. Like the rest of the family, the Quotient leaves
that use values of Mathlib's `map` keep the named premise `BaseChangeMkQFormula` as an instance
argument (`quotFunctor` itself does not need it). The focused test
[Quotient](../../../AglibTest/AlgebraicGeometry/Grassmannian/Quotient.lean) restates the results
with the instance from `BaseChangeFormula` and guards their axioms. The general lemmas used here are
in sibling leaves of their owners: `Modules/Pullback/FreeComp`, `Modules/FittingIdeal/ConstantRank`,
`Descent/Modules/ZariskiEpi`, `CategoryTheory/Sites/Descent/OfEpi` and
`Algebra/Category/ModuleCat/ChangeOfRings/SpanSingleton`. `AlgSpecPoints.isOpenImmersion_coverPt`
and `AlgSpecPoints.exists_coverPt_apply_eq` are in [Injectivity](Quotient/Injectivity.lean).

[Quotient/Kernel](Quotient/Kernel.lean) gives the kernel `q.kernel` of a quotient with its inclusion
`q.kernelι` into `O^n` and the short exact sequence `0 → K → O^n → Q → 0` (`shortExact`), which
splits locally (`exists_local_splitting`). Its formation commutes with pullback along every
morphism, with no flatness: `pullbackKernelIso f q : f^* q.kernel ≅ (q.pullback f).kernel`
commutes with the inclusions through `pullbackFreeIso` (`pullbackKernelIso_hom_kernelι`), and
isomorphic quotients have isomorphic kernels (`IsoUnder.kernelIso`). Nitsure,
arXiv:math/0504590v1, §5, p. 26 (`K_Y = φ^* ker(f)`).

[Quotient/KernelRank](Quotient/KernelRank.lean) proves that the kernel is finite locally free of
rank `n - k` (`isFiniteLocallyFree_kernel`, `sheafHasRank_kernel`); on a nonempty scheme `k ≤ n`
(`rank_le_of_nonempty`).

[Quotient/UniversalKernel](Quotient/UniversalKernel.lean) defines the universal kernel
`universalKernel R k n`, the kernel of `universalQuotientRep R k n`, finite locally free of rank
`n - k`. If `P` represents the class classified by `g`, then `g^*` of the universal kernel is
`P.kernel` under `O^n` (`pullbackUniversalKernelIso`, `pullbackUniversalKernelIso_hom_kernelι`;
Nitsure, §5, p. 26). The classifying map `classifyingMap P` is natural
(`classifyingMap_pullback`) and detects isomorphism under `O^n`
(`classifyingMap_eq_classifyingMap_iff`). Premise BCF.

[Quotient/UniversalQuotientPullback](Quotient/UniversalQuotientPullback.lean): the classifying map of
the pullback of `universalQuotientRep R k n` along `φ : T ⟶ schemeOver R k n` is `φ`
(`classifyingMap_pullback_universalQuotientRep`). Premise BCF.

[Quotient/Reindex](Quotient/Reindex.lean) transports quotients of `SheafOfModules.free I`, for
`e : I ≃ ULift (Fin n)`, to quotients of `O^n` (`ofFree`, inverse `toFree`), compatibly with
pullback on the nose (`ofFree_pullback`), through `freeReindexIso` (Mathlib's `freeMap e`). The
kernel of `π` in `free I` is the kernel of `ofFree e π hQ` (`ofFreeKernelιIsKernel`,
`ofFreeKernelIso`). With BCF, the Grassmannian classifies these quotients
(`existsUnique_isoUnder_ofFree`), and the universal kernel included into `free I`,
`universalKernelιFree`, pulls back to the kernel of `π` (`pullbackUniversalKernelIsoOfFree_hom_ι`).

[Finiteness](Finiteness.lean) shows that `scheme R k n` is quasi-compact and that `toBase R k n` is
quasi-compact and locally of finite type; over a Noetherian `R` the scheme is Noetherian
(instances, also for `(schemeOver R k n).left` and `.hom`). The proof uses the finitely many charts
`Spec (R[Φ]/I)` (Stacks, Tag 089T, proof). Premise BCF.

The focused test [Kernel](../../../AglibTest/AlgebraicGeometry/Grassmannian/Kernel.lean) restates
these results with the BCF instance and guards their axioms. Relocation candidates:
`freeReindexIso`, `pullback_map_freeReindexIso_hom`/`_inv`,
`pullbackFreeIso_inv_freeReindexIso_inv` and `epi_pullbackFreeIso_inv_comp` in
[Quotient/Reindex](Quotient/Reindex.lean) belong in `Modules/Pullback` (namespace `Scheme.Modules`),
and `finiteType_chartRing` in [Finiteness](Finiteness.lean) belongs in `RingTheory/Grassmannian`.

Relocation candidates (general, not specific to the Grassmannian): `algSpecPoints`,
`algSpecPointsEquiv` and `AlgebraicGeometry.AlgSpecPoints.*` in
[FunctorOfPoints](FunctorOfPoints.lean), and `Grassmannian.locAway` and
`Grassmannian.span_range_eq_top_of_forall_notMem` in [Representability](Representability.lean),
belong to a lower owner for schemes over `Spec R`. After such a move, `exists_chartLocal` can be
derived from `AlgSpecPoints.exists_locAway_comp_eq`.

## Projective space as `Gr(R^m, 1)`

The leaves in `ProjectiveSpace/` compare the Grassmannian of rank-one quotients with Aglib's
polynomial projective space (part of plan row F9; quasi-projective morphisms remain open). Fix a
labeling `e : ι ≃ Fin m` of the homogeneous coordinates.

[Charts](ProjectiveSpace/Charts.lean) identifies the chart ring at `e_{e i}` with the standard chart
ring `B_i = coordinateRing R ι i`, by `Φ_{0j} ↦ X_{e⁻¹ j}/X_i` (`chartToCoordinate`,
`coordinateToChart`, `chartCoordinateEquiv`). Over `B_{il} = Away(X_i X_l)` the chart sections from
`i` and `l` differ by the unit `X_i/X_l`, so their chart points agree (`ofChartSection_overlap`),
and the Grassmannian overlap `Away(det_IJ)` is `B_{il}` (`overlapChartEquiv`). The `R`-algebra
structure on `B_i` is `awayAlgebra`
([ProjectiveSpace/AwayAlgebra](../ProjectiveSpace/AwayAlgebra.lean)); the general chart facts used
here are in
[RingTheory/Grassmannian/CoordinateChart](../../RingTheory/Grassmannian/CoordinateChart.lean).

[Comparison](ProjectiveSpace/Comparison.lean) glues `toGrassmannian` on the standard cover and
`ofGrassmannian` on the Grassmannian charts and proves both inverse laws:
`grassmannianIso e : scheme R 1 m ≅ ProjectiveSpace R ι` and, over `Spec R`,
`grassmannianOverIso e : schemeOver R 1 m ≅ ProjectiveSpace.schemeOver R ι`. This is Stacks,
Tag 089V (Lemma 27.22.3), over any base ring and for every `m`, proved by chart gluing.

[FunctorOfPoints](ProjectiveSpace/FunctorOfPoints.lean) transports the functor of points. Maps
`Spec A ⟶ P` over `Spec R` are the points of `G(1, A ⊗[R] R^m; A)` (`representableEquiv`,
`representableIso`). Maps `T ⟶ P` over `Spec R` are the natural transformations
`algSpecPoints T ⟶ Module.Grassmannian.functor 1` (`homEquivNatTrans`), so `P` represents
`localFunctor R 1 m` (`localFunctorRepresentableBy`). The identity classifies the coordinate
quotient on each `D₊(Xᵢ)` (`homEquivNatTrans_id_app_chartOver`), and these chart values
characterize it (`natTrans_ext_of_chartOver`, `eq_id_of_representableEquiv_chartOver`). Chart
sections give maps through `D₊(Xᵢ)` (`representableEquiv_symm_ofChartSection`).

[UniversalQuotient](ProjectiveSpace/UniversalQuotient.lean) shows that the chart quotients of the
universal point are the frame coefficients, in the frame `Xᵢ`, of the quotient map
`coordinatePowerGeneratingMap R ι 1 : O^ι ↠ O(1)` given by the coordinate sections
(`awayToSection_chartRatioSection`), and that the chart sections transform by the twisting
transition unit `coordinateTransitionUnit` (`overlapRight_chartRatioSection`).

[Quotient](ProjectiveSpace/Quotient.lean) gives the description of maps `T ⟶ P` by rank-one
locally free quotients (Stacks, Tags 089V and 01NE): `ProjectiveSpace.quotFunctorRepresentableBy R e
: (quotFunctor R 1 m).RepresentableBy (ProjectiveSpace.schemeOver R ι)` composes
`localFunctorRepresentableBy` with `localFunctorIsoQuotFunctor R 1 m`. It covers quotients of
`O^m = SheafOfModules.free (ULift (Fin m))`; the form with `O^ι` needs reindexing along `e`, and
the identification of the universal quotient with `coordinatePowerGeneratingMap R ι 1 : O^ι ↠ O(1)`
is open.
