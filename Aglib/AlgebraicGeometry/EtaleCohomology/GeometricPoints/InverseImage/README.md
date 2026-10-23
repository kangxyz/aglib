# Inverse image on original geometric stalks

For arbitrary schemes `X S : Scheme.{u}`, any morphism `f : S ⟶ X`, any
separably closed field `Ω : Type u`, geometric point `η : Spec Ω ⟶ S`, and
every actual `L : AbelianSheaf.{u,u+1} X`, the original canonical map
`stalkUnit f η L` is an isomorphism. The result uses no finite-local-constant,
Ext, locally-finite-type, or other geometric premise.

| Source | Interface |
| --- | --- |
| [InverseImage](../InverseImage.lean) | Constructs the native skyscraper-adjunction mate and proves its component is the original `stalkUnit`; gives `stalkUnit_isIso` and the natural isomorphism `stalkUnitNatIso`. |
| [Projection](Projection.lean) | Records that the native skyscraper unit evaluates to the original colimit germ. |
| [Skyscraper](Skyscraper.lean) | Reindexes actual points under inverse image and compares the original skyscraper sheaves. |

The natural isomorphism has the actual functor shape

```lean
stalkUnitNatIso f η :
  (pointSmallEtale (η ≫ f)).sheafFiber ≅
    inverseImage f ⋙ (pointSmallEtale η).sheafFiber
```

`stalkUnitNatIso_hom` identifies each component definitionally with the original
`stalkUnit`. `germ_stalkUnitNatIso` retains the original section, the native
inverse-image adjunction unit, and `pulledBackPoint`; coefficient-map
naturality is retained. When a finite representation is supplied,
`stalkUnitNatIso_app_eq` identifies this isomorphism with the existing
represented-coefficient `stalkUnitIso`. No representation is required for the
general result.

This extends the standard-value stalk comparison to arbitrary morphisms. The
separate fibrewise-closed isomorphism-detection consumer retains its
`LocallyOfFiniteType` premise; that condition is not used for `stalkUnit`
itself. Wider coefficient universes and proper base change are outside scope.
