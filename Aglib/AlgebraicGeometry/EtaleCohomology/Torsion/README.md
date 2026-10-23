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

## Genuine module injectives

[ZModCohomology](ZModCohomology.lean) discharges the generic terminal-object
and over-category finite-product conditions on the actual small-etale site,
with coefficient value universe `u + 1`. Its acyclicity theorem retains an
independently supplied `HasExt.{e}`; the standard endpoint supplies
`HasExt.{u+1}` from native enough injectives and concludes positive
cohomology vanishing without a separate Ext-existence premise. No scheme
finiteness or modulus restriction is imposed.

Injectivity is assumed in the genuine module-valued sheaf category, and the
conclusion concerns its original underlying abelian cohomology. The
module-injective pullback criterion still needs acyclicity of the actual
pulled-back underlying injectives; that geometric input remains open.
Finite cogeneration, existence of finite presentations for arbitrary finite
locally constant or constructible coefficients, the local proper-base-change
criterion and general proper base change also remain open.
