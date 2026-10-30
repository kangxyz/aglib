# Curves over fields

Declarations about field curves belong to
`AlgebraicGeometry.Scheme.OverField.Curve`. `Curve.Properties X` records smooth
relative dimension one, properness and geometric connectedness of the actual
`X : Scheme.OverField.FScheme F`. `Scheme.OverField.PointedGroupLaw X o` keeps
Mathlib's native `GrpObj X` and equality of its identity section with the
specified origin `o`.

The source cohort is `R5Lab.Aglib.AlgebraicGeometry.{Curves,ProjectiveSpace}` at
R5Lab revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Native mathematical
names replace the historical application namespaces. Projective-space embedding
and pencil providers live in the sibling `ProjectiveSpace` family. This family
uses the existing native scheme, module, cohomology, relative-Picard and finite
morphism providers.

| Exact import | Interface and hypotheses |
| --- | --- |
| `Aglib.AlgebraicGeometry.Curves.Core` | Connectedness, Noetherianity, field base change, integrality and closed-stalk consequences; the original normality, regularity and dimension theorem-family arguments remain explicit. |
| `Aglib.AlgebraicGeometry.Curves.SmoothGeometry` | Proved geometric integrality, rational-origin DVR stalks and the pointed-morphism application, using native smooth-curve and group-rigidity suppliers. |
| `Aglib.AlgebraicGeometry.Curves.Genus.BaseChange` | Actual structural-field H1 finrank genus and invariance along arbitrary structural field maps; the original proper base-change argument remains explicit. |
| `Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse` | Actual fractional-ideal divisor sheaves, the divisor/Picard correspondence and residue-weighted line-bundle degree. Retains integral, Noetherian, closed-DVR, dimension and principal-product-formula conditions. |
| `Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula` | The proved proper-curve principal product-formula family with original residue weights and scalar action, using native proper cohomology finiteness. |
| `Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula` | The proved all-field finite norm/order family, summing all maximal branches with actual residue degrees. No separability or perfectness condition is inserted. |
| `Aglib.AlgebraicGeometry.Curves.Projectivity.AffineMap` | A proper integral dimension-one scheme over any field has an affine morphism to the literal projective line, through the existing finite native-line map and its original comparison isomorphism. |
| `Aglib.AlgebraicGeometry.Curves.Projectivity.Integral` | Actual projective embedding of the original proper integral dimension-one field scheme, preserving its structural triangle. |
| `Aglib.AlgebraicGeometry.Curves.Duality` | Actual canonical Ext/cohomology duality on a smooth curve with a closed projective embedding, retaining coefficient finiteness and original structural field actions. |
| `Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle` | The proved `LineBundleRiemannRoch` family for actual line bundles, their actual O(D)-transferred degree and H0/H1 finranks. Closed-DVR, dimension, properness and constants hypotheses remain explicit. |
| `Aglib.AlgebraicGeometry.Curves.PointDivisor.Sections` | Actual powers of the dual ideal of a specified rational point on a smooth proper geometrically connected curve. In genus one, positive powers have H1 zero and H0 dimension n over the original arbitrary field; original inclusions and the first constant-one section are retained. See the [point-divisor guide](PointDivisor/Sections.md). |
| [PointDivisor.PoleFunctions](PointDivisor/PoleFunctions.md) and [Products](PointDivisor/Products.md) | On the same pointed genus-one curve, normalized field-linear maps send actual point-pole sections into the original function field. Native tensor multiplication agrees with field multiplication for all natural pole bounds, including zero. |
| [PointDivisor.AffineComplement](PointDivisor/AffineComplement.md) | On an integral smooth proper curve of relative dimension one, a rational function with negative order at the supplied closed point and regular away from it gives a finite projective-line map whose affine-chart inverse image is exactly the original point complement. |
| `Aglib.AlgebraicGeometry.Curves.RiemannRoch.HighDegreeVanishing` | The literal original high-degree H1 vanishing family on actual line bundles. Smoothness and constants are derived from the original regular proper curve hypotheses. |
| `Aglib.AlgebraicGeometry.Curves.RiemannHurwitz.CanonicalDegree` | The proved `SmoothCanonicalDegree` family, with actual canonical line bundle and degree `2g - 2`, preserving all original conditions. |
| `Aglib.AlgebraicGeometry.Curves.RelativePicard.Representability` | Conditional all-field, all-genus representability of the existing normalized degree-zero Picard classes on every test scheme, including explicit local Noetherianity of the representer. |
| `Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme` | From `Curve.Properties X` alone, over any field: dimension one, flatness, a closed immersion `X ⟶ P^N_k` over `Spec k`, and `exists_representableBy_fppfPicardSheaf_properties`, a separated scheme locally of finite type representing `Pic_{X/k,(fppf)}` of `X.hom` on locally Noetherian test schemes with items 1–3 of `exists_representableBy_fppfPicardSheaf_basicProperties` and the statements of `exists_representableBy_fppfPicardSheaf_fieldProperties` for `X.hom` and `H^1(X, 𝒪_X)`. The embedding-dependent Hilbert strata are in `Jacobian.DegreeStrata`. |
| `Aglib.AlgebraicGeometry.Curves.Jacobian.AbelMorphism` | For `X` smooth of relative dimension one and proper with a rational point `o` and any representation `R` by `P`: the Abel morphism `abelMorphism o ho P R n : X^n ⟶ P`, the Yoneda image of the class of `BoundedFamily.lineBundle`, with value `Σ (s_i - o_T)` on tuples; `(o, …, o)` goes to the unit; for a curve its image lies in `Pic⁰` and is closed when `P` is separated. |
| `Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints` | For `X ⟶ Spec k` with a section, proper and flat with geometrically integral fibres (Kleiman Thm 2.5(2)): `Pic(X) ≃+ Pic_{X/k,(fppf)}(k)`, the rational point `picardPoint P R L` of a class, and `picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral : Pic(X) ≃+ Additive (Spec k ⟶ P)` for the group law of any representing `P` locally of finite type. |
| `Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeStrata` | Riemann–Roch as `χ(X, L) = deg L + 1 - g`. For a curve `X ⊆ P^N_k` and any representing `P`, the rational point of a class `c` lies in the stratum of `φ` (Kleiman (4.8.1), `χ(X_t, L_t^{-1}(n)) = φ(n)`) if and only if `φ(n) = n · deg O(1) + 1 - g - deg c`, so in the stratum of `m ↦ m · deg O(1) + 1 - g - d` if and only if `deg c = d`; the strata are open and closed and the degree-zero one contains the unit. Other points of `P` are not described. Any field. |
| `Aglib.AlgebraicGeometry.Curves.Jacobian.IdentityComponent` | Over an algebraically closed field, for `P` locally of finite type and separated and an open and closed `Z` containing the unit whose points `picardPoint P R L` have degree zero: `a_g(X^g) = Z = Pic⁰_{X/k}`, the rational points of `Pic⁰` are the degree-zero classes, and `Pic⁰` is proper. Also `Curve.Properties.exists_rationalPoint_of_isAlgClosed`. |
| `Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero` | The Jacobian `J = Pic⁰_{X/k}` over an algebraically closed field, for every representing `P` locally of finite type and separated: `J` is proper, is the image of `abelMorphism o ho P R g` for every rational point `o` and the degree-zero stratum of every embedding, and `degreeZeroAddEquivOfIsAlgClosed : ker deg ≃+ Additive (Spec k ⟶ J)`. Smoothness and `dim J = g` are not treated. |
| `Aglib.AlgebraicGeometry.Curves.Jacobian.Multiplication` | Over an algebraically closed field, for `Curve.Properties X`, every separated `P` locally of finite type representing `Pic_{X/k,(fppf)}` and `n` invertible in `k`: on `J = Pic⁰_{X/k}` (`identityComponentOver P.obj`), `[n] = (𝟙 J) ^ n` is finite (`isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed`) and surjective (`surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed`), its `k`-point fibres are finite and `J(k)` is `n`-divisible; `Pic⁰(X) = ker deg` is `n`-divisible (`exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed`, `surjective_nsmul_curveDegree_ker_of_isUnit_of_isAlgClosed`, with no `P` in the statement). Uses `degreeZeroAddEquivOfIsAlgClosed` and `finite_picard_torsion`, so the module imports the étale-cohomology closure through `EtaleCohomology.Finiteness.KummerCurveTorsion`; smoothness of `J`, `dim J = g` and `deg [n]` are not used. |
| `Aglib.AlgebraicGeometry.Curves.GenusOneGroupLaw` | Exact-origin genus-one group law transported from the selected Picard representing witness; the general representability premise remains explicit. |

The [pointed Weierstrass presentation](../EllipticCurve/Weierstrass/Presentation.md)
constructs a native equation with nonzero discriminant from `Curve.Properties X`,
`coherentGenus k X = 1` and the original rational section over `k`. Its actual
isomorphism over that same arbitrary field preserves the specified section as
the literal infinity section. The construction uses the original pole sections,
their products and the affine complement; no group law or Picard representer
is supplied as a premise.

`ProjectiveLine.Charts` constructs the literal homogeneous Proj over an arbitrary
commutative ring. `ProjectiveLine.TwoChart` constructs the literal polynomial
pushout under `Scheme.ProjectiveLine.TwoChart`; its source is Quillen revision
`8273990b7977bd87edfe94cd2be91dec64de79aa`. `ProjectiveLine.Comparison` preserves
both original chart arrows and the structural map. The new owner avoids
colliding with the historical global Quillen names. The projectivity graph
uses this pure geometry without the optional older Laurent-module H1 proof.
`ProjectiveLine.Native` retains the actual over-field isomorphism from literal
homogeneous P1 to finite-coordinate projective space lifted to the field universe.
[Projectivity/AffineMap](Projectivity/AffineMap.lean) owns
`OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1`, with the
proper, integral and dimension-one hypotheses on the original field scheme.
Picard smoothness imports this lower curve result.
The general integral separated retraction theorem lives outside the curve family,
in `Aglib.AlgebraicGeometry.Morphisms.GeometricRetraction`.

The generic graph-difference line bundles and their origin trivialization live
in `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphLineBundle`,
under `Scheme.Hom`, for arbitrary bases and test schemes. The field degree,
normalization and inverse constructions retain their `Curve.Abel` owner.
General structural-field actions on module stalks live in
`Aglib.AlgebraicGeometry.Modules.Stalk.FieldScalars`, under `Scheme.Modules`,
and reuse the existing native cohomology stalk-scalar object and germ formula.
Only the residue-weighted curve-degree wrapper remains in the curve family.

The source-only `Projectivity` import facade is represented by the exact
`Projectivity.Integral` import. The unused conditional standard-coherent-finiteness
product-formula corollary can be expressed by applying the unconditional
`Picard.Degree.properCurveProductFormula`; no second finiteness implementation
is retained.

`RiemannRoch.HighDegreeVanishing` realizes the original high-degree H1 vanishing
interface using actual Riemann–Roch, canonical degree and canonical Ext duality.
The all-test representability interface remains an explicit premise. Existing
Abel inverse recovery on locally Noetherian tests and representability-dependent
inverse laws do not independently discharge that general representability input.

`AglibTest.CurveCore` checks native original-object provider types, original chart
arrows, structural field base change, prescribed-origin data and the literal
high-degree vanishing factory. Compilation,
source-policy checks and mathematical adoption retain their separate scopes.

Focused interface guides: [Actual model component geometry](Models/Components/README.md).

[Isogeny.Etale](Isogeny/Etale.md) proves the characteristic-zero finite
surjective curve-group homomorphism family and binds it to the original
pointed proper-curve consumer.

## Point classes and Picard restriction

[PointDivisor/IdealClass](PointDivisor/IdealClass.lean) identifies the divisor of
the rational-point ideal inclusion with that point on an integral Noetherian
scheme with DVR closed stalks. In dimension at most one its dual has the native
point-divisor Picard class, without a trivializing chart in the final theorem.
`PointDivisor/PoleFunctions` consumes these shared arguments.

[Picard/PointDegree](Picard/PointDegree.lean) gives degree one for a rational
point line bundle over any field. Over algebraically closed constants a closed
point supplies degree and modulo-degree surjectivity.
[Picard/OpenRestriction](Picard/OpenRestriction.lean) proves Picard restriction
surjective for every open immersion into the curve; if a closed point is missed,
its restriction on degree-zero classes is surjective. These two pure providers
have no Jacobian or étale-cohomology module in their Aglib dependency closure.

[Picard/DegreeQuotient](Picard/DegreeQuotient.lean) identifies the original
`Pic(X)/n` with `ZMod n` over algebraically closed constants for `n` invertible
in the field, using point degree and A4 divisibility.
[Picard/OpenDivisibility](Picard/OpenDivisibility.lean) combines open restriction
with A4 to give `n`-divisibility of the actual open Picard group under the same
conditions. A4 retains its existing étale-finiteness input described above.
