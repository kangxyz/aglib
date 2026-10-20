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

## Monoidal localization through chosen isomorphisms

[Monoidal/Induced](Monoidal/Induced.lean), imported as
`Aglib.CategoryTheory.Localization.Monoidal.Induced`, works in Mathlib's
namespace `CategoryTheory.Localization.Monoidal`. Let `L : C ⥤ D` be a
localization functor at a monoidal class `W`, with Mathlib's localized
monoidal structure `LocalizedMonoidal L W ε`. For objects `Mᵢ` with chosen
isomorphisms `eᵢ : L.obj Aᵢ ≅ Mᵢ`, `μOf e₁ e₂ : M₁ ⊗ M₂ ≅ L.obj (A₁ ⊗ A₂)`
transports Mathlib's tensor comparison `μ`. The lemmas `map_tensorHom_eq`,
`map_whiskerRight_comp_associator_eq`, `map_leftUnitor_hom_comp`,
`map_rightUnitor_hom_comp` and `μOf_hom_comp_map_braiding` express the
localized tensor maps, associator, unitors and braiding through `μOf` as
images under `L` of the structure maps of `C`, in exactly the shape of the
equations of `Monoidal.InducingFunctorData` and of the braiding condition of
`BraidedCategory.ofFaithful`. Objects, morphisms and isomorphisms are
arbitrary, and the file imports only Mathlib. Its consumer is the
[monoidal structure on scheme modules](../../AlgebraicGeometry/Modules/Tensor/Monoidal/README.md).

[SerreKernel](SerreKernel.lean) supplies `CategoryTheory.Functor.isLocalization_comp_kernel` and
transport along actual equivalences and natural isomorphisms. Composition retains
the original exactness and kernel-Serre-localization hypotheses on both functors;
no localization premise is discharged by renaming an arbitrary functor.
