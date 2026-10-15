# Coproduct comparison and split pushouts

[NatTransCoproduct](NatTransCoproduct.lean), imported as `Aglib.CategoryTheory.Limits.NatTransCoproduct`, gives `CategoryTheory.NatTrans.isIso_app_coproduct` for the actual coproduct comparison with the source's preservation and componentwise-isomorphism hypotheses. [FiniteCoproductFunctor](../Abelian/FiniteCoproductFunctor.lean) separately supplies finite-limit/finite-colimit preservation of finite coproducts in the abelian setting.

`CategoryTheory.Limits.IsPushout.isSplitMono_inr` is the generic split-pushout result in [DegreewiseSplitMono](../../Algebra/Homology/CochainComplex/DegreewiseSplitMono.lean): in an arbitrary category, a chosen pushout square with split first input has split opposite inclusion. No abelian structure is needed for this lower square statement.

Finite-free sheaf tensors and degreewise split cochain pushout arguments consume these actual universal-property maps. Product/coproduct index and universe hypotheses are preserved by each source statement.

[BiproductPushout](BiproductPushout.lean), imported as `Aglib.CategoryTheory.Limits.BiproductPushout`, proves `CategoryTheory.Limits.IsPushout.biprod_map`: the literal biproduct maps of two displayed pushout squares form a pushout in a preadditive category with binary biproducts. No mono or splitting premise is required. [Shapes](Shapes/README.md) owns displayed cokernel-to-pushout and zero-coproduct results. The [identity-cone functor](../../Algebra/Homology/MappingCone/README.md) consumes these universal-property primitives.
