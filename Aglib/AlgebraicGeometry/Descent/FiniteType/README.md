# Finite-type property descent and closed hulls

These results use a small cofiltered diagram `D : I ⥤ Scheme.{u}`, with
`I : Type u`, `[Category.{u} I]`, affine transition maps, a cone `c`, and
`hc : IsLimit c`. They retain the actual cone projections and later arrows
`j : Over i`. Finite presentation is not a standing hypothesis.

## Closedness and separatedness after base change

Import `Aglib.AlgebraicGeometry.Descent.FiniteType.EventualClosedImmersion`
for [EventualClosedImmersion](EventualClosedImmersion.lean).
In `AlgebraicGeometry.Scheme`,
`exists_isClosedImmersion_baseChangeOverHom_of_isLimit D c hc i a` takes an
actual `a : A ⟶ B` in `Over (D.obj i)`, with qcqs `A.left` and `B.left` and
`[LocallyOfFiniteType a.left]`. If its actual limit base change is a closed
immersion, it gives a later `j : Over i` with

```lean
IsClosedImmersion (baseChangeOverHom (D.map j.hom) a)
```

The hypothesis at the limit uses
`baseChangeOverHom (c.π.app i) a`. The base stages themselves need not be
affine or qcqs, and `a` need not be finitely presented.

Import `Aglib.AlgebraicGeometry.Descent.FiniteType.Separated` for
[Separated](Separated.lean).
`Scheme.exists_isSeparated_pullback_fst_of_isLimit D c hc i f` takes
`f : X ⟶ D.obj i` with qcqs `X` and `[QuasiCompact f]`. From
`IsSeparated (pullback.fst (c.π.app i) f)` it gives
`∃ j : Over i, IsSeparated (pullback.fst (D.map j.hom) f)`.
This theorem has no finite-type or finite-presentation hypothesis on `f`.
It compares the original diagonal with its actual base change.

## A fixed target and varying sources

Import `Aglib.AlgebraicGeometry.Descent.FiniteType.SeparatedFixedTarget`
for [SeparatedFixedTarget](SeparatedFixedTarget.lean).
`Scheme.exists_isSeparated_app_of_isLimit_of_quasiSeparatedSpace` instead
assumes qcqs stages and a quasi-separated fixed target `S`. Its data include
`t : D ⟶ (Functor.const I).obj S`, a separated `h : c.pt ⟶ S`, and
`∀ j, c.π.app j ≫ t.app j = h`. For each initial `i`, it supplies a later
`j : Over i` for which `t.app j.left` is separated. Compactness of `S` is not
required. This is the separatedness input for the closed-hull construction.

## Closed finite-presentation hulls

Import `Aglib.AlgebraicGeometry.Descent.FiniteType.IntegerFiniteTypeHull`
for [IntegerFiniteTypeHull](IntegerFiniteTypeHull.lean).
`Scheme.exists_separated_finitePresentation_factorization_of_integerFiniteType_isLimit`
adds that every stage map `Products.toIntegerBase (D.obj i)` is locally of
finite type and quasi-compact. For a separated locally finite-type
`f : c.pt ⟶ S` with quasi-separated `S`, it returns a qcqs `Y`, a closed
immersion `e : c.pt ⟶ Y`, and a separated finitely presented `g : Y ⟶ S`
with `e ≫ g = f`. The diagram and its limit remain premises of this theorem.

[FinitePresentationHull](FinitePresentationHull.lean), imported as
`Aglib.AlgebraicGeometry.Descent.FiniteType.FinitePresentationHull`, gives the
underlying `exists_separated_finitePresentation_factorization_of_isLimit`
with qcqs stages whose integer structural maps are locally finitely
presented, quasi-compact and quasi-separated. The
[unconditional hull](../../Morphisms/FiniteType/README.md) constructs the
required arithmetic system for a compact source and removes the supplied
diagram premise. [Qcqs compactification](../../Compactification/QCQS.md)
uses the same conditional hull inside its two-diagram assembly.
