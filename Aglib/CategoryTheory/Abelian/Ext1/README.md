# Fixed-endpoint extensions and degree-one Ext

This family uses the actual derived `CategoryTheory.Abelian.Ext` and short complexes of an arbitrary abelian category. Its declarations live under `CategoryTheory.Abelian.Ext1`.

| Leaf | Interface and conditions |
| --- | --- |
| [Extension](Extension.lean) | `Extension X Y` records `Y → middle → X` and its actual short exactness, with definitionally fixed endpoints. `Extension.toShortComplex` retains those maps. Under `HasExt.{w} C`, `Extension.extClass` is the canonical `Ext.{w} X Y 1`. `Extension.Iso` is a middle-object isomorphism commuting with both endpoint maps. |
| [Equality](Equality.lean) | `Extension.Iso.toShortComplexIso` has identity endpoint components. Under `HasExt.{w} C`, `extClass_eq_iso` turns equality of canonical Ext classes into an actual fixed-endpoint extension isomorphism. |
| [Representability](Representability.lean) | Under `HasDerivedCategory.{w'} C`, `shortExact_of_singleTriangle_distinguished` and `singleδ_eq_of_distinguished` recover short exactness and the canonical connecting map from the displayed distinguished triangle. Under `HasExt.{w} C`, `exists_extension` realizes every `Ext.{w} X Y 1` by an actual extension with precisely that class. |

All leaves retain `C : Type u`, `Category.{v} C` and `Abelian C`; the object, hom, Ext and explicitly supplied derived-category universes remain separate. The Ext realization and equality proofs choose `HasDerivedCategory.standard C` internally. They add no enough-injective or enough-projective hypothesis.

Focused imports are `Aglib.CategoryTheory.Abelian.Ext1.{Extension,Equality,Representability}`. The latter two depend only on `Extension` within Aglib. Mathlib owns the Ext construction, short-exact extension class, single-functor and distinguished-triangle operations; this family supplies their fixed-endpoint realization/equality interface for general extension and torsor constructions. It does not introduce an alternative Ext object or an unproved quotient classification.
