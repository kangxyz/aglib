# Finite surjective morphisms and geometric-point lifting

[GeometricPoints](GeometricPoints.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricPoints`, gives `AlgebraicGeometry.Scheme.Finite.GeometricPoints.exists_lift`. For a finite surjective scheme map `f : X ⟶ Y` and an algebraically closed field-valued point `y : Spec K ⟶ Y`, there is an actual scheme map `x : Spec K ⟶ X` with `x ≫ f = y`.

`exists_lift_over` proves the relative version over an arbitrary base scheme: equality is of the whole morphisms in `Over`, including the structural map, rather than merely of underlying points. Schemes and fields retain the stated universe `u`.

No etale premise or rational point over the original field of definition is assumed. The result works on the actual finite geometric fibre and is a public lower lifting interface. [Finite coherent direct image](../../Modules/Coherent/Pushforward/Finite/README.md) is a separate consumer interface for the same native morphism class.
