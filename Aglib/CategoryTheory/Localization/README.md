# Localization from actual approximation functors

[Approximation](Approximation.lean), imported as
`Aglib.CategoryTheory.Localization.Approximation`, owns
`CategoryTheory.Localization.Restriction`. The data is a full faithful functor
`F : C ⥤ D`, a morphism property `W` on `D`, a family of functors `T i : D ⥤ C`
preserving the induced weak equivalences and actual counits `T i ⋙ F ⟶ 𝟭 D`.
For every pair `X,Y : C`, some common index must make both counit components
at `F.obj X` and `F.obj Y` belong to `W`.

The original inclusion and approximations descend to the actual constructed
localizations. Source and target counits, their component equations and their
compatibility retain the given original maps. The pairwise condition proves
that the localized inclusion is fully faithful; a uniform counit index is not
assumed. Essential surjectivity or an equivalence is not supplied by this
criterion. The bounded-above derived-category localization uses good truncation
as this actual approximation family.
