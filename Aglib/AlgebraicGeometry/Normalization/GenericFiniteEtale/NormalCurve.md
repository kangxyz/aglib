# Etaleness from the generic and codimension-one stalks

`NormalCurve.lean` supplies the geometric curve argument used by
`Aglib.AlgebraicGeometry.Morphisms.Etale.NormalCurveInertia`.

The extracted source is
`R5Lab.Aglib.AlgebraicGeometry.Normalization.NormalCurvePurity` at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e9581abb5be829a48e08470ac47e77caf953f58103dce915b7c540b0a7aac94c`,
lines 39–141. The native namespace is
`AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.NormalCurve`.

Source lines 39–74 retain every embedding of the literal original chart algebra
into `AlgebraicClosure X.functionField`. `chartAlgebraPoint` uses the existing
native `localOriginalIso` to construct a geometric point of the same original
cover. Equality of every original point under a given absolute Galois automorphism
then gives equality of every chart-algebra embedding by faithfulness of `Spec`.
This argument never replaces the set of original points by selected embeddings.

Source lines 77–101 split each target stalk's dimension into zero or one under
`topologicalKrullDim X ≤ 1`. In the zero case, integrality identifies the actual
point with `genericPoint X`. Source lines 102–112 use the existing
`genericFiberOverIso` to recover the original finite-etale generic cover as the
actual normalization pullback. No smoothness of generic inclusion is assumed.

Source lines 113–141 retain an integral locally Noetherian target with every
actual stalk integrally closed. Native `GenericFiniteEtale.Finite` supplies the
finite normalization structural morphism and hence the finite-presentation
condition used by `LocalRing.Etale`'s actual stalk-base-change neighborhood
criterion. The dimension split supplies an etale neighborhood at every source
point, and these neighborhoods cover the whole actual relative normalization.
The input at dimension one is still etaleness of every actual codimension-one
target-stalk pullback.

The normalization and structural map are the native relative normalization of
`C.obj.hom ≫ X.fromSpecStalk (genericPoint X)` and its `.fromNormalization`.
No connectedness, integrality or nonemptiness of the cover or its normalization
is imposed; split and empty covers remain covered. There is no characteristic,
perfect-residue-field, excellence, regular-surface, or Zariski–Nagata premise.
