# Torsion on the small-etale site

This family specializes the generic
[site torsion construction](../../../CategoryTheory/Sites/Torsion/README.md)
to the actual small-etale abelian sheaves `AbelianSheaf.{u,u+1} X`.

| Source | Scope |
| --- | --- |
| [Basic](Basic.lean) | Internal torsion, allowing different positive annihilators locally, is equivalent to torsion in every original geometric stalk. It uses the actual stalk family and needs no Ext or finite-type premise. |
| [Inverse image](InverseImage.lean) | Pullback along any scheme morphism preserves internal torsion by the original all-coefficient `stalkUnit` isomorphism. No finite-type, Ext or cohomology premise is added. |
| [Colimit](Colimit.lean) | Every internally torsion abelian étale sheaf is the actual filtered colimit of its native factorial annihilator kernels through their original inclusions. |
| [General comparison](Comparison.lean) | Original cohomology pullback for an internally torsion coefficient is bijective if both original cohomology functors preserve all `ℕ`-shaped colimits in every degree and the stated genuine prime-module comparisons are bijective. Independent source/target Ext universes are retained through the native `ULift` natural transformation. |
| [Qcqs comparison](QcqsComparison.lean) | For a morphism between qcqs schemes, coefficient continuity supplies the sequential-colimit premise. All-degree bijectivity for every genuine prime `ZMod p`-module sheaf implies all-degree bijectivity for every internally torsion coefficient, with independent Ext universes. |
| [Surjectivity criterion](SurjectivityCriterion.lean) | For every modulus, including zero and one, degree-zero injectivity and surjectivity in every degree below `q`, on all genuine module coefficients, give injectivity in degree `q`; all-degree surjectivity and degree-zero injectivity give all-degree bijectivity. On qcqs source and target, the corresponding genuine prime-module tests suffice for every internally torsion coefficient, with independent Ext universes. |
| [ZMod cohomology](ZModCohomology.lean) | The original underlying functor on genuine `ZMod n`-module sheaves preserves finite limits and colimits. The underlying abelian coefficient of an injective genuine module sheaf has zero positive original `Sheaf.H`, for every modulus, including zero and one. |
| [Module-injective criterion](InjectiveCriterion.lean) | For an actual étale ring sheaf `R`, comparison for underlying `R`-module coefficients follows from degree-zero comparison for all such modules and positive cohomology vanishing for the actual pulled-back underlying sheaves of injective module sheaves. The module, source-abelian and target-abelian Ext universes remain independent. |

## Coefficient continuity and torsion comparison

For a qcqs `X : Scheme.{u}`,
`qcqsCohomologyFunctor_preservesColimitsOfShape` supplies preservation by
the original `cohomologyFunctor X n` of filtered diagrams indexed by a
small category `I : Type (u + 1)`, retaining
`HasExt.{e} (AbelianSheaf.{u,u+1} X)` and
`HasColimitsOfShape I AddCommGrpCat.{e}`.
`qcqsCohomologyFunctor_preservesSequentialColimits` then supplies
`ℕ`-shaped preservation for arbitrary independent `e` through the actual
equivalence with `AsSmall.{u+1} ℕ`.

For `f : S ⟶ X` with both schemes qcqs,
`cohomologyPullback_bijective_of_prime_modules_qcqs` therefore requires
no separate continuity premise. Its remaining hypothesis is bijectivity of the
literal original pullback in every degree for every sheaf valued in
`ModuleCat.{u+1} (ZMod p)`, for every prime `p`. The coefficient under
test is its original underlying abelian sheaf. This prime comparison is an
application input.

## Surjectivity tests for original pullback

[SurjectivityCriterion](SurjectivityCriterion.lean) uses the literal
`cohomologyPullback` of the original underlying abelian sheaf of a genuine
`ZMod n`-module sheaf. For every `n`, including zero and one,
`zmodCohomologyPullback_injective_of_surjective_below` gives injectivity
in degree `q` from degree-zero injectivity for every such module coefficient
and surjectivity in every degree `k < q` for every such coefficient.
`zmodCohomologyPullback_bijective_of_surjective` upgrades all-degree
surjectivity and degree-zero injectivity to bijectivity in all degrees.

These two results allow an arbitrary `f : S ⟶ X`. The torsion consequence
`cohomologyPullback_bijective_of_prime_modules_surjective_qcqs` requires
both schemes to be qcqs. Degree-zero injectivity and all-degree surjectivity
for every genuine prime `ZMod p`-module coefficient then imply all-degree
bijectivity for every `F` with `IsTorsion X F`.
The source and target `HasExt.{e}` and `HasExt.{e'}` universes remain
independent. Sequential continuity is supplied by the qcqs theorem above;
the original prime-module test hypotheses remain explicit.

## Genuine module injectives

[ZModCohomology](ZModCohomology.lean) discharges the generic terminal-object
and over-category finite-product conditions on the actual small-etale site,
with coefficient value universe `u + 1`. Its acyclicity theorem retains an
independently supplied `HasExt.{e}`; the standard endpoint supplies
`HasExt.{u+1}` from native enough injectives and concludes positive
cohomology vanishing without a separate Ext-existence premise. No scheme
finiteness or modulus restriction is imposed.

Injectivity is assumed in the genuine module-valued sheaf category, and the
conclusion concerns its original underlying abelian cohomology.
`SurjectivityCriterion` uses this source acyclicity. It does not assume
injectivity after scalar forgetting or pullback. The earlier
module-injective pullback criterion still needs acyclicity of the actual
pulled-back underlying injectives; that geometric input remains open.

## Exact comparison from colimits and test coefficients

The generic
[effacement comparison](../../../Algebra/Homology/DerivedCategory/Ext/EffacementComparison.lean)
and [cogenerator comparison](../../../Algebra/Homology/DerivedCategory/Ext/CogeneratorComparison.lean)
apply to abelian categories `C,D,E`, additive functors
`U : C ⥤ D` and `F : D ⥤ E` preserving finite limits and colimits,
objects `X : D`, `A : E`, and an actual map `a : A ⟶ F.obj X`.
The comparison is the original `F.extPrecompMap a (U.obj Y) q`.
The Ext universes `w` for `D` and `w'` for `E` remain independent.

Assume `C` has enough injectives and, for every injective `I : C`,
all positive original `Ext X (U.obj I)` groups vanish. This is source
acyclicity of the actual coefficient images. For each `Y : C`, supply an
actual diagram `K Y : J Y ⥤ C` with colimit cocone point `Y`, every
stage in a class `P`, and an actual monomorphism from every `P` object
into an object of a test class `T`.

`extPrecompMap_bijective_on_image_of_cogenerators` concludes all-degree
bijectivity from degree-zero injectivity on every coefficient, all-degree
surjectivity on `T`, and preservation of every displayed diagram by
`U ⋙ F ⋙ extFunctorObj A q`. The
[surjective-colimit step](../../../Algebra/Homology/DerivedCategory/Ext/SurjectiveColimit.lean)
needs only this target cohomological preservation. Source Ext preservation
and colimit preservation by `U` alone are not required for that step.

`extPrecompMap_bijective_on_image_of_cogenerator_tests` also reduces
degree-zero injectivity to `T`. For each `J Y`, colimits in
`AddCommGrpCat.{max w w'}` must exist and their `colim` functor must
preserve monomorphisms. Both degree-zero functors
`U ⋙ extFunctorObj X 0` and `U ⋙ F ⋙ extFunctorObj A 0` must preserve
the actual diagram `K Y`. These are the additional hypotheses of the
[injective-colimit step](../../../Algebra/Homology/DerivedCategory/Ext/InjectiveColimit.lean);
the independent Ext universes are compared by the native `ULift`
natural transformation.

Geometric constructible presentations and finite cogenerators, geometric
prime/curve-test surjectivity, and the geometric local proper-base-change
application remain open. The abstract criterion receives those presentations,
embeddings and test comparisons as inputs. General proper base change and
acyclicity of the actual pulled-back underlying module injectives also remain
open.
