# Pushouts in an actual full subcategory

[Pushout](Pushout.lean), imported as `Aglib.CategoryTheory.Limits.FullSubcategory.Pushout`, proves `CategoryTheory.ObjectProperty.isPushout_lift`. Let `P` be an object property on a category `D`, let `F : C ⥤ D`, and supply `hF : ∀ X, P (F.obj X)`. If the four actual `F`-images of a square form a pushout in `D`, the same square mapped by `P.lift F hF` is a pushout in `P.FullSubcategory`.

The chosen apex is already among the values certified by `hF`. No closure of `P` under arbitrary pushouts, additive structure or exact-category structure is assumed. The proof uses the fully faithful inclusion and preserves the original arrows and universal property.

Use this leaf to retain a known pushout after lifting a functor into its full-subcategory codomain. [Selected exact subcategories](../../ExactCategory/README.md) have additional hypotheses for an inherited exact structure; [sequential colimits](../Shapes/SequentialSystem/README.md) are a separate limits family.
