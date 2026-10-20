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
| `Aglib.AlgebraicGeometry.Curves.Projectivity.Integral` | Actual projective embedding of the original proper integral dimension-one field scheme, preserving its structural triangle. |
| `Aglib.AlgebraicGeometry.Curves.Duality` | Actual canonical Ext/cohomology duality on a smooth curve with a closed projective embedding, retaining coefficient finiteness and original structural field actions. |
| `Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle` | The proved `LineBundleRiemannRoch` family for actual line bundles, their actual O(D)-transferred degree and H0/H1 finranks. Closed-DVR, dimension, properness and constants hypotheses remain explicit. |
| `Aglib.AlgebraicGeometry.Curves.RiemannRoch.HighDegreeVanishing` | The literal original high-degree H1 vanishing family on actual line bundles. Smoothness and constants are derived from the original regular proper curve hypotheses. |
| `Aglib.AlgebraicGeometry.Curves.RiemannHurwitz.CanonicalDegree` | The proved `SmoothCanonicalDegree` family, with actual canonical line bundle and degree `2g - 2`, preserving all original conditions. |
| `Aglib.AlgebraicGeometry.Curves.RelativePicard.Representability` | Conditional all-field, all-genus representability of the existing normalized degree-zero Picard classes on every test scheme, including explicit local Noetherianity of the representer. |
| `Aglib.AlgebraicGeometry.Curves.GenusOneGroupLaw` | Exact-origin genus-one group law transported from the selected Picard representing witness; the general representability premise remains explicit. |

`ProjectiveLine.Charts` constructs the literal homogeneous Proj over an arbitrary
commutative ring. `ProjectiveLine.TwoChart` constructs the literal polynomial
pushout under `Scheme.ProjectiveLine.TwoChart`; its source is Quillen revision
`8273990b7977bd87edfe94cd2be91dec64de79aa`. `ProjectiveLine.Comparison` preserves
both original chart arrows and the structural map. The new owner avoids
colliding with the historical global Quillen names. The projectivity graph
uses this pure geometry without the optional older Laurent-module H1 proof.
`ProjectiveLine.Native` retains the actual over-field isomorphism from literal
homogeneous P1 to finite-coordinate projective space lifted to the field universe.
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
