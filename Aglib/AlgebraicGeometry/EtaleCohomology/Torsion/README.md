# Torsion on the small-etale site

This family specializes the generic [site torsion construction](../../../CategoryTheory/Sites/Torsion/README.md)
to the actual small-etale abelian sheaves `AbelianSheaf.{u,u+1} X`.

| Source | Scope |
| --- | --- |
| [Basic](Basic.lean) | Internal torsion, allowing different positive annihilators locally, is equivalent to torsion in every original geometric stalk. It uses the actual stalk family and needs no Ext or finite-type premise. |
| [Inverse image](InverseImage.lean) | Pullback along any scheme morphism preserves internal torsion by transport along the original all-coefficient `stalkUnit` isomorphism. No finite-type, Ext, or cohomology premise is added. |
| [Colimit](Colimit.lean) | Every internally torsion abelian etale sheaf is the actual filtered colimit of its native factorial annihilator kernels, through their original inclusions. |
| [Original comparison](Comparison.lean) | Bijectivity of the original cohomology pullback for an internally torsion coefficient reduces to prime `ZMod` module-sheaf tests, assuming both original cohomology functors preserve all `ℕ`-shaped colimits in every degree and the stated prime-comparison endpoints. Independent source/target Ext universes are retained through the native `ULift` natural transformation. |
| [Module-injective criterion](InjectiveCriterion.lean) | For an actual etale ring sheaf `R`, original cohomology pullback for the underlying abelian sheaf of an `R`-module sheaf follows from degree-zero pullback bijectivity for all such modules and positive-degree vanishing for the actual pulled-back underlying sheaves of injective module sheaves. The module, source-abelian, and target-abelian `HasExt` universes remain independent. These tests are premises; injectivity after forgetting or after inverse image is not asserted. |

The colimit presentation is a sheaf-theoretic source for bounded-torsion
devissage. The comparison theorem keeps cohomological colimit preservation and
the prime comparisons as explicit hypotheses; this family proves neither input.
It does not prove cohomological filtered-colimit continuity, constructibility,
finite cogeneration, the local proper-base-change criterion, or proper base
change.

## Native validation

The comparison, inverse-image, and module-injective criterion providers were
included in the eleven-leaf native batch `remote-688042ffc6d9448c8b4933075b2da7f5`.
Generated entries, style, and the selected declaration linters passed; the
pinned axiom audit reported only the standard foundations. This validates the
compiled conditional interfaces. The cohomological colimit, prime-module,
degree-zero, and pulled-back-injective vanishing inputs above remain explicit;
no proper-base-change conclusion is made.
