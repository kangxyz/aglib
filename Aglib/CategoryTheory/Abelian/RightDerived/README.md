# Actual right-derived objects and integer resolution complexes

[Cochain](Cochain.lean) defines
`InjectiveResolution.isoRightDerivedObjCochain F I n` for an additive
functor between arbitrary abelian categories and a supplied actual
injective resolution in a category with enough injectives. Its source is
the unchanged native `(F.rightDerived n).obj M`. Its target is native
homology in degree `(n : ℤ)` of the original integer resolution after
termwise application of `F`.

The forward map is exactly the original `I.isoRightDerivedObj F n`, the
inverse original extension-homology comparison, and homology of the
inverse original `I.cocomplex.mapExtendIso F embeddingUpNat`.
`isoRightDerivedObjCochain_hom` records those three factors, and
`isoRightDerivedObjCochain_hom_naturality` retains every supplied original
resolution lift and the actual `F.rightDerived` coefficient map.

Source and target object and morphism universes are independent. The
comparison requires no exactness of `F` or derived-category structure.
Actual affine higher-direct-image computation and open restriction use
these same objects and maps.
