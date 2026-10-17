# Charts and Zariski descent of the Grassmannian functor

This family extends Mathlib's `Module.Grassmannian` (`Mathlib/RingTheory/Grassmannian.lean`):
`G(k, M; R)` is the set of submodules of `M` whose quotient is finite projective of constant
rank `k`, and `Module.Grassmannian.functor k : CommAlgCat R ⥤ Type _` sends `A` to
`G(k, A ⊗[R] M; A)` with base change `Module.Grassmannian.map`. Every statement below is about
these actual objects. Sources: Stacks, Tag 089T (proof of representability of `G(k, n)`);
Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, "Construction of
Grassmannian", pp. 7–8.

| Leaf | Main declarations | Hypotheses |
| --- | --- | --- |
| [BaseChange](BaseChange.lean) | `BaseChangeMkQFormula` (named premise), `baseChangeMkQ_tmul`, `baseChangeMkQQuotEquiv` | `baseChangeMkQ_tmul` assumes `BaseChangeMkQFormula`; the class and `baseChangeMkQQuotEquiv` assume nothing |
| [Chart](Chart.lean) | `chart`, `chartFunctor`, `map_mem_chart`, `mem_chart_map_iff`, `chartEquiv`, `map_ofChartSection`, `chartEquiv_map` | arbitrary `M` |
| [ChartRing](ChartRing.lean) | `ChartRing`, `chartSectionsEquivAlgHom`, `chartFunctorCorepresentableBy` | `M = Fin n → R`, algebras in the universe of `R` |
| [Overlap](Overlap.lean) | `transitionMatrix`, `mem_chart_iff_isUnit_det` | arbitrary `M` |
| [ChartIntersection](ChartIntersection.lean) | `chartTransitionDet`, `chartInterCorepresentableBy`, `chartTransitionIso`, `chartFamilyInterCorepresentableBy` | `M = Fin n → R`, finite families |
| [Covering](Covering.lean) | `exists_localizedModule_bijective`, `exists_mem_chart_map`, `baseChange_localization_bijective_iff` | `M = Fin n → R` |
| [ChartLocus](ChartLocus.lean) | `mem_chart_of_map_localization`, `exists_mem_chart_map_of_bijective` | arbitrary `M` |
| [Descent](Descent.lean) | `eq_of_map_localization_eq`, `rTensor_mem_map_iff_of_isLocalization`, `finite_projective_rankAtStalk_of_localizationSpan` | `span (range s) = ⊤` |
| [Gluing](Gluing.lean) | `exists_map_localization_eq` | finite `s`, `span (range s) = ⊤` |

**Charts.** For `x : Fin k → M`, `chart R x` is the set of points `N` for which
`chartMap x N : R^k → M ⧸ N`, `e_b ↦ [x b]`, is bijective (Mathlib's TODO item). Base change
preserves the condition, so `chartFunctor R x : Subfunctor (functor k)` takes the chart at
`b ↦ 1 ⊗ x b` over each `A`. More precisely, `map f N` lies in the chart exactly when the base
change of `chartMap` along `f` is bijective (`mem_chart_map_iff`, and
`mem_chart_map_iff_of_algebraMap` for a given algebra structure with algebra map `f`).

**Chart points as linear sections.** `chartEquiv A x` identifies the chart over `A` with the
`R`-linear maps `φ : M → A^k` with `φ (x b) = e_b`; the point is `ker (φ.liftBaseChange A)`.
`map_ofChartSection` computes Mathlib's base change of such a point as the point of
`f ∘ φ`.

**Chart rings.** For `M = Fin n → R`, `ChartRing R x = R[Φ_{a j}] ⧸ (Φ X - 1)`, where `X` has
columns `x b`. `chartFunctorCorepresentableBy R x` is a
`Functor.CorepresentableBy` for `(chartFunctor R x).toFunctor` on `CommAlgCat.{u} R` by
`CommAlgCat.of R (ChartRing R x)`. For a coordinate tuple `x b = e_{I b}` the relations make
the `I`-columns of `Φ` the identity. For injective `I` (an ordering of a `k`-subset of `Fin n`)
this is Nitsure's `Z[X^I]` base-changed to `R`; for non-injective `I` the relations force
`1 = 0`, so the chart ring is zero and the chart is empty.

**Overlaps and covering.** A chart point lies in the chart at `y` exactly when
`det (φ (y b) a)` is a unit (`mem_chart_iff_isUnit_det`): the intersection of two charts is a
basic open of either one. For `M = Fin n → R` the intersection subfunctor
`chartFunctor R x ⊓ chartFunctor R y` is corepresented by
`Localization.Away (chartTransitionDet x y)` (`chartInterCorepresentableBy`), and the two
descriptions of the intersection are related by
`chartTransitionIso R x y : Away (chartTransitionDet x y) ≅ Away (chartTransitionDet y x)`, whose
`hom` is the ring map of Nitsure's `θ_{y,x} : U^y_x → U^x_y` (`I = y`, `J = x`). It is the
identity on underlying points
(`chartInterCorepresentableBy_homEquiv_transitionIso_hom`); for `y = x` the determinant is a
unit and the transition is the identity (`isUnit_chartTransitionDet_self`,
`chartTransitionIso_self`). The intersection of a chart with
finitely many others is corepresented by the localization away from the product of the transition
determinants (`chartFamilyInterCorepresentableBy`). For
every point and prime `p` there are a coordinate tuple `I` and `r ∉ p` such that the base change
of the point along every `R`-algebra map inverting `r` lies in the coordinate chart at `I`
(`exists_mem_chart_map`). Membership in any chart is Zariski local, and bijectivity of the chart
map at a prime spreads to a basic open neighbourhood (`ChartLocus`).

**Zariski descent.** For `s : ι → A` generating the unit ideal, a point is determined by its
base changes to the `Localization.Away (s i)` (`eq_of_map_localization_eq`). For finite `ι`,
points over the `Localization.Away (s i)` whose base changes agree on overlaps glue
(`exists_map_localization_eq`); the overlap of `i` and `j` is any localization of
`Localization.Away (s j)` away from `s i`, with an `R`-algebra map from
`Localization.Away (s i)` compatible with the maps from `A`.

**Module exposure and the named premise.** Mathlib's `baseChangeMkQ`, `baseChangeMkQEquiv` and
`map` have unexposed bodies; in module-system sources (such as Aglib's) that do not `import all`
`Mathlib.RingTheory.Grassmannian`, even `baseChangeMkQ.eq_1` is unknown, and
the public API (`baseChangeMkQ_surjective`, `map_toSubmodule`, `map_id`, `map_comp`, `functor`)
does not determine the values of `map`. Therefore `BaseChange.lean`
states the component formula `baseChangeMkQ B N (b ⊗ m) = b ⊗ [1 ⊗ m]` as the Prop-valued class
`BaseChangeMkQFormula.{u, v, w} R M`, and every declaration whose statement or proof depends on
the values of Mathlib's `map` (charts as subfunctors, the base-change criteria, the
corepresentations, overlaps, covering, chart loci, separatedness and gluing) takes it as an
instance argument. Mathlib's definition satisfies the formula; an upstream `@[expose]` on
`Module.Grassmannian.baseChangeMkQ`, or an upstream `baseChangeMkQ_tmul`, would supply the
instance. Statements that do not depend on the values of `map` (`chartEquiv`, the chart rings
and their algebra-map
equivalence, `mem_chart_iff_isUnit_det`, `exists_localizedModule_bijective`,
`map_toSubmodule_of_algebraMap`, `finite_projective_rankAtStalk_of_localizationSpan`) carry no
premise.

[BaseChangeFormula](BaseChangeFormula.lean) supplies the instance
`baseChangeMkQFormula : BaseChangeMkQFormula R M` for every ring and module, so importing it
makes the results above unconditional. It is the only leaf that uses `import all`
(of `Mathlib.RingTheory.Grassmannian`), as a documented one-file exception in
`scripts/check_library_layout.py`. Delete the leaf and the exception once Mathlib exposes
`baseChangeMkQ` or publishes `baseChangeMkQ_tmul`; the instance can then be proved from the
public API.

`Covering.lean` contains the general helper `baseChange_localization_bijective_iff`
(`g.baseChange (Localization S)` is bijective exactly when `LocalizedModule.map S g` is), and
`Descent.lean` the general `finite_projective_rankAtStalk_of_localizationSpan`; both are
candidates for a lower module or localization owner.

The present consumer is [AlgebraicGeometry/Grassmannian](../../AlgebraicGeometry/Grassmannian/README.md).
