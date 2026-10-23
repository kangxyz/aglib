# Torsion sheaves on a site

This family develops internal torsion for abelian sheaves on an arbitrary
Grothendieck site. Torsion is local and sectionwise: each original section is
annihilated on a covering sieve by some positive integer, which may vary with
the section and the cover. No single global annihilator is assumed.

| Source | Reusable construction |
| --- | --- |
| [Basic](Basic.lean), [points](Points.lean), [sheaves](Sheaf.lean) | Local torsion sieves, coefficient naturality, and the equivalence with torsion in a chosen small conservative family of original point fibres. |
| [Annihilators](Annihilator/Basic.lean) and [section comparison](Annihilator.lean) | The native kernel subsheaf of multiplication by `n`, its literal inclusion, and its original section-level kernel comparison. |
| [Factorial diagram](Annihilator/Diagram.lean) and [colimit](Colimit.lean) | The positive stages killed by `(n+1)!` and the actual filtered-colimit presentation, with the original inclusions and coefficient naturality. |
| [Devissage](Devissage.lean) | The native short exact annihilator/quotient sequence and the stated bounded-torsion prime-devissage property theorem. Its property theorem retains its zero-object, prime-killed, and short-exact-extension hypotheses. |
| [Property reduction](Reduction.lean) | An isomorphism-invariant property of abelian sheaves reduces from internally torsion to prime-annihilated objects, assuming it contains zero objects and is stable under actual short-exact extensions and the displayed `ℕ`-colimits. The module-coefficient form uses prime `ZMod p` sheaves and retains `[UnivLE.{max u v, w}]`. |
| [ZMod modules](ZMod/Basic.lean) | Conversion of a sheaf killed by the literal scalar identity into a genuine `ZMod n`-module sheaf while retaining its original sections, restriction maps, coefficient arrows, and underlying-sheaf isomorphism. |
| [ZMod injectives](ZMod/Injectives.lean) | Genuine `ZMod n`-valued sheaves on the standard-sized site have enough injectives and `HasExt`, for every `n`, including zero. This is a result in the module-valued sheaf category. |
| [ZMod underlying cohomology](ZMod/Cohomology.lean) | The actual genuine-module underlying functor preserves finite limits and colimits for every modulus. Under the displayed terminal, over-product and Ext hypotheses, injective genuine module sheaves have acyclic original underlying abelian coefficients in every positive degree. |
| [ZMod fullness](ZMod/Full.lean) | Every original additive arrow between supplied genuine ZMod actions is linear, so the original module and sheaf underlying functors are full, for every modulus including zero. |
| [Finite presentations](FinitePresentation.lean) | Native free scalar-quotient generators and actual finite generator/relation cokernel data give finite presentability, original finite-stage factorization and a colimit certificate for the original Hom cocone, under explicitly sized evaluation continuity. |
| [Original Ext comparison](../../../Algebra/Homology/DerivedCategory/Ext/ShortExactComparison.lean) | The actual exact-functor comparison is natural and stable under zero objects, isomorphisms and short-exact extensions. It is stable at an actual colimit cocone when both original Ext functors preserve that colimit. Independent Ext universes are related by an explicit native `ULift` natural transformation. |
| [Composite Ext comparison](../../../Algebra/Homology/DerivedCategory/Ext/CompositeComparison.lean) | If the first actual comparison is bijective in all degrees, the second in degree zero, and positive Ext vanishes on actual composite images of source injectives, the second comparison is bijective. Injectives need not be preserved by either functor; all three Ext universes remain independent. |
| [Ringed ZMod bridge](ZMod/Ringed.lean) | For every site and every modulus, including zero, genuine `ZMod n`-module sheaves are equivalent to native `SheafOfModules` over the associated sheaf of the actual constant `RingCat` presheaf on `ULift (ZMod n)`. The comparison retains the original underlying module sheaf and is natural. |

For torsion sheaves, the factorial annihilator stages present the original sheaf
as a filtered colimit through the actual kernel inclusions. The result is an
objectwise torsion presentation; it does not assert cohomological continuity,
constructible finite cogenerators, a local criterion, or proper base change.

The `ZMod` conversion includes `n = 0`, with the canonical native `Int` module
structure. Its generic site statement uses the displayed `HasSheafCompose`
premise; native preservation supplies it under `UnivLE.{max u v, w}`, including
the standard coefficient universe. In that genuine module-valued sheaf category,
[ZMod injectives](ZMod/Injectives.lean) supplies enough injectives and `HasExt`
in the standard universe for every modulus, including zero. The separate
[ringed bridge](ZMod/Ringed.lean) identifies these module sheaves with modules
over the associated sheaf of the constant ring. It makes no claim that a
module-sheaf injective is injective after forgetting to abelian sheaves or that
module Ext agrees with abelian-sheaf Ext.

## Free scalar quotients and finite presentations

[Generators](FinitePresentation/Generators.lean) uses the existing
`Hypercohomology.freeAbelianSheaf`. The actual
`freeZModRepresentable J n U` is the native cokernel of multiplication by
`n` on this free representable. Its Hom equivalence identifies maps to
`F` with original sections of `F` on `U` killed by `n`, retaining
the original quotient and coefficient maps. The comparison between evaluation
and the honest Hom universe uses the explicit native `ULift`. The coefficient
category is `Sheaf J AddCommGrpCat.{max v t}` under the displayed
sheafification hypothesis.

[Compactness](FinitePresentation/Compactness.lean) retains an actual finite
generator family `U0 : Fin r0 → C`, relation family `U1 : Fin r1 → C`,
relation arrow `d`, quotient arrow `q`, equation `d ≫ q = 0`, and
`IsColimit (CokernelCofork.ofπ q hdq)`. Evaluation on every selected
generator and relation object must satisfy
`PreservesFilteredColimitsOfSize.{k,k} (evaluation J U)`. These data imply native `IsFinitelyPresentable.{k} F`.

[FinitePresentation](FinitePresentation.lean) then factors every original
`a : F ⟶ c.pt` through an original stage of any supplied filtered colimit
cocone: `b ≫ c.ι.app i = a`. It also supplies
`IsColimit ((coyoneda.obj (op F)).mapCocone c)`.
All natural moduli, including zero and one, and empty finite generator or
relation families are allowed. The
[small-etale geometric consumer](../../../AlgebraicGeometry/EtaleCohomology/Constructible/README.md)
supplies evaluation continuity on chosen qcqs objects. Existence of such
presentations for arbitrary finite locally constant or constructible
coefficients remains open.

## Exact underlying coefficients and acyclicity

[ZMod/Cohomology](ZMod/Cohomology.lean) proves preservation of finite limits
and finite colimits by the original
`sheafCompose J (forget₂ (ModuleCat (ZMod n)) AddCommGrpCat)`.
The module and abelian values have universe `max u v`, for a site with
object universe `u` and morphism universe `v`; the result allows every
`n`, including zero and one.

For acyclicity, the theorem retains
`HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})`, finite products in
`Over W` for every site object `W`, and a supplied terminal object.
For an injective genuine module sheaf `I`, the original underlying
abelian sheaf has trivial positive `Sheaf.H.{e}`. The construction uses
the actual ringed-module equivalence and its original underlying natural
isomorphism. The hypothesis is injectivity in the module-valued sheaf category;
the conclusion is underlying abelian cohomological acyclicity.
The [scheme consumer](../../../AlgebraicGeometry/EtaleCohomology/Torsion/ZModCohomology.lean)
supplies the site conditions and also a native standard Ext endpoint.
