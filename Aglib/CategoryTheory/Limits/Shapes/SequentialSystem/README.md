# Sequential colimits and alternating-sign maps

The namespace is `CategoryTheory.Limits.SequentialSystem`. Each leaf is a focused import under `Aglib.CategoryTheory.Limits.Shapes.SequentialSystem` and works with the actual natural-number diagram and its original transition maps.

[IsoColimit](IsoColimit.lean) constructs `toZeroIso`, `constIso`, `cocone` and `isColimit` for a sequence `f n : X n ⟶ X (n + 1)` in an arbitrary category when every `f n` is invertible. The cocone with vertex `X 0`, whose legs are the successive inverse-transition composites, is a colimit. With a chosen colimit, `colimitIso` compares it with `X 0`; `ι_colimitIso_hom` identifies each original colimit leg followed by this comparison with `(toZeroIso f n).hom`. For an actual functor `F : ℕ ⥤ C`, `reconstructionIso`, `colimitIsoOfSucc` and `ι_colimitIsoOfSucc_hom` give the same comparison from invertibility of all actual successor maps.

[TailColimit](TailColimit.lean) defines the final indexing functor `shiftFunctor t`, sending `n` to `t + n`. For `F : ℕ ⥤ C` with `HasColimit F`, `tailColimitIso F t` identifies the colimit of the tail with `colimit F`. The equations `tailColimitIso_ι_hom` and `tailColimitIso_ι_inv` identify both comparison directions on the original stage `t + n` inclusions. Transition-map invertibility is not required for this finite-tail result.

[EventuallyIsoColimit](EventuallyIsoColimit.lean) proves `colimit_ι_isIso_of_tail`: if `F` has a colimit and every successor map at stage `n ≥ i` is invertible, then the original arrow `colimit.ι F i` is invertible. There is no condition on earlier transitions. When all successors are invertible, `colimit_ι_zero_eq_inv` identifies the stage-zero leg with `(colimitIsoOfSucc F).inv`.

[SignCorrection](SignCorrection.lean) works in a preadditive category. Given stage maps `a n : F.obj n ⟶ G.obj n` satisfying

```lean
F.map (homOfLE (Nat.le_succ n)) ≫ a (n + 1) =
  -(a n ≫ G.map (homOfLE (Nat.le_succ n)))
```

`signCorrectionHom a h` is a natural transformation with component `(-1 : ℤ) ^ n • a n`, as stated by `signCorrectionHom_app`. If the stage maps are the forward maps of specified isomorphisms `e n`, `signCorrectionIso e h` is a natural isomorphism with those alternating components. `alternatingIso_hom` and `signCorrectionIso_hom_app` fix the signs, and `signCorrectionHom_eq_iso_hom` identifies its forward transformation with the same morphism construction. No colimit-existence or transition-isomorphism premise is needed for sign correction.

The [limits guide](../../README.md) locates the other categorical universal-property interfaces. These leaves supply general colimit and sign comparisons for downstream sequential homological constructions without importing those applications.
