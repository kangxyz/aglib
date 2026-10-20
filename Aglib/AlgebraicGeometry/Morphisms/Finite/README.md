# Finite morphisms and field-valued point lifts

[GeometricPoints](GeometricPoints.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricPoints`, gives `AlgebraicGeometry.Scheme.Finite.GeometricPoints.exists_lift`. For a finite surjective scheme map `f : X ⟶ Y` and an algebraically closed field-valued point `y : Spec K ⟶ Y`, there is an actual scheme map `x : Spec K ⟶ X` with `x ≫ f = y`.

`exists_lift_over` proves the relative version over an arbitrary base scheme: equality is of the whole morphisms in `Over`, including the structural map, rather than merely of underlying points. Schemes and fields retain the stated universe `u`.

No etale premise or rational point over the original field of definition is assumed. The result works on the actual finite geometric fibre and is a public lower lifting interface. [Finite coherent direct image](../../Modules/Coherent/Pushforward/Finite/README.md) is a separate consumer interface for the same native morphism class.

[PointLifts](PointLifts.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.Finite.PointLifts`, proves `AlgebraicGeometry.Scheme.Finite.finite_hom_over_field`: for a finite morphism `f : Y ⟶ Spec K`, the set of sections over `K` is finite. More generally, `finite_hom_over_point` proves finiteness of the actual Hom set `Over.mk x ⟶ Over.mk f` for a finite morphism `f : Y ⟶ X` and any field-valued point `x : Spec K ⟶ X`. These are the lifts `g : Spec K ⟶ Y` satisfying `g ≫ f = x`. The field is arbitrary, and neither an etale nor a surjectivity premise is imposed. This finiteness conclusion allows an empty lift set; the geometric-point existence results above retain their separate surjectivity and algebraically closed field hypotheses. The [finite etale family](../FiniteEtale/README.md) uses these finite-Hom results for its actual field-valued fibre functor.

[ClosedPoints](ClosedPoints.lean) maps actual closed points through the supplied finite map.
Its generic stalk equation and units map belong to the lower
`FunctionField.StalkMap`, under `Scheme.functionFieldMap_stalk` and
`Scheme.functionFieldUnitMap`, and need only integral source/target and
dominance. [Norm](Norm.lean) defines `Scheme.Hom.ClosedFibre`, relative residue algebra,
integer residue degree (`residueDegreeInt`, the cast of Mathlib's native
`f.residueDegree`), field degree and actual field norm. [LocalNormAlgebra](LocalNormAlgebra.lean), under
`Scheme.Hom.LocalNormAlgebra`, constructs the localization of the entire inverse
image of an affine target neighbourhood at its actual point. It gives the
actual pullback over the target stalk, all maximal branches, their bijection
with all actual closed fibre points, canonical stalk and residue comparisons,
and their exact residue degrees. Integral source/target, finite dominance,
affine/neighbourhood and nonempty conditions remain as displayed. Noetherianity
is explicit in the closed-fibre/residue-degree portion; the final freeness and
norm comparison require the actual target stalk to be a DVR. `FiniteNorm` is
the separate algebraic supplier and permits inseparable fraction extensions.
[GeometricDegree](GeometricDegree.lean) defines `Scheme.OverField.HasGeometricDegree` by cardinality
of every actual algebraically closed geometric fibre in the stated universe;
it supplies no rank-to-cardinality theorem. [Birational](Birational.lean) constructs
`Scheme.finiteBirationalIso` with the supplied finite map as its hom, assuming
both schemes integral, actual target `NormalStalks`, and invertibility over a
specified nonempty open. It assumes neither source normality nor dimension.
