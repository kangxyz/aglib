# Quasicoherent coefficients and original étale cohomology

This family starts from an actual `F : X.Modules` with
`F.IsQuasicoherent`. Its small-etale additive coefficient is
`additiveCoefficient X F : AbelianSheaf.{u,u+1} X`. There is no
coefficient-flatness, finite-generation or Noetherian premise.

| Source | Original object or map |
| --- | --- |
| [AdditiveSections](AdditiveSections.lean), [AdditiveDescent](AdditiveDescent.lean) | Values are lifted sections of the actual pullback module. Restrictions use the native geometric unit, typed Hom transport and pullback coherence; descent holds on the small site and big étale slice. |
| [CoefficientMaps](CoefficientMaps.lean) | Actual native module morphisms induce `additiveCoefficientMap`, with identity, composition and section formulas. |
| [AffineAcyclicity](AffineAcyclicity.lean), [AmitsurExactness](AmitsurExactness.lean) | Actual finite affine étale families use faithfully flat Amitsur exactness for arbitrary modules. |
| [ZariskiAdjunction](ZariskiAdjunction.lean), [ZariskiRestriction](ZariskiRestriction.lean) | The actual opens-to-small-etale functor supplies exact inverse image and left exact restriction. Restriction is not assumed exact on unrelated coefficients. |
| [ZariskiModuleComparison](ZariskiModuleComparison.lean), [ZariskiModuleNaturality](ZariskiModuleNaturality.lean) | The restricted additive coefficient is identified with the actual lifted native Zariski module coefficient, retaining its original map square. |

## Affine acyclicity

[AffineVanishing](AffineVanishing.lean) proves
`affineObject_ext_eq_zero` for every affine étale test object and
`affine_cohomology_eq_zero` for every affine `X`. Positive original
`Sheaf.H (additiveCoefficient X F)` vanishes, with independently supplied
`HasExt.{e}`. Arbitrary modules, including nonflat and infinitely generated
ones, are allowed.

The lower [basis criterion](../../../CategoryTheory/Sites/SheafCohomology/BasisAcyclicity/README.md)
uses the actual cofinal affine-family basis and original tuple complexes.
The proof supplies affine acyclicity from actual Amitsur descent; it does not
use it as a hypothesis of its own comparison.

## Global Zariski and module comparison

For every scheme, [ZariskiComparison](ZariskiComparison.lean) defines

```lean
zariskiRestrictionCohomologyMap X A n :
  Sheaf.H ((zariskiRestriction X).obj A) n →+ Sheaf.H A n
```

by the original exact-inverse-image/counit comparison. It is natural for every
additive coefficient arrow. For `A = additiveCoefficient X F` it is
bijective in every degree, with independent source/target Ext universes.
No separatedness or qcqs assumption on `X` is required.

[ModuleCohomologyComparison](ModuleCohomologyComparison.lean) supplies the
native-source equivalence

```lean
Sheaf.H.{e} (Scheme.Cohomology.moduleAddSheaf X F) n ≃+
  Sheaf.H.{e'} (additiveCoefficient X F) n
```

It retains the genuine Zariski value universe `u`, étale value universe
`u+1`, and independent `e,e'`. The value lift and actual restriction
isomorphism give this equivalence. Naturality holds for native module
morphisms and for additive coefficient arrows whose original restriction
square commutes. This includes the additive scalar/Frobenius transports used
by the [curve family](../Curves/README.md), without treating semilinear
Frobenius as a linear endomorphism in the original scalar structure.
