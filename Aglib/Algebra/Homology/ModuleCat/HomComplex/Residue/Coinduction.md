# The intrinsic coefficient line of derived residue coinduction

Let R be a regular local ring of dimension two and k an arbitrary field
with its original finite local R-algebra structure. The map R→k need not
be surjective, and the extension of residue fields need not be separable.
The ring and module carriers lie in one universe, matching the finite-length
Ext supplier; the two derived-category model universes are independent.

`ModuleCat.derivedResidueCoinduction R k` is the installed
`(coextendScalars (algebraMap R k)).rightDerivedFunctorPlus` applied to the
original ring module in degree zero. `derivedResidueCoefficientLine R k`
is **its own native degree-two homology**, already a k-module. Neither is
defined by transporting a module structure from Ext or by choosing a
one-dimensional vector-space identification with k.

## Original model and scalar action

For every supplied injective resolution I of the original R-module R,
`derivedResidueResolutionIso` identifies the literal termwise coinduced
complex with the same installed derived object. The `_hom` theorem states
that this is the installed derived unit followed by the inverse of the
image of the original resolution inclusion. The `_unit` theorem retains
the original augmentation square exactly.

At each actual resolution term, `residueCoinductionComplex_smul_apply`
states the native action `(a·phi)(b)=phi(b*a)`. The ordinary coinduction
counit is evaluation at the original unit, as stated in
`residueCoinductionComplex_counit_apply`. This is the actual restricted
R-module counit; no field trace or additional derived trace is asserted.

The canonical residue map k→ResidueField(k) is bijective. Its field-module
isomorphism is `fieldResidueModuleIso`, whose forward-value theorem is the
original residue map. Source precomposition by this map and the existing
`regularSingleComplexIso` evaluation at one identify the actual residue
Hom complex with the actual coinduced complex. This use of the residue
quotient is unrelated to an orientation of the new coefficient line.

`derivedResidueHomologyIso` composes the original derived-resolution
homology comparison, native localization/homology factors, and that chain
isomorphism. It is an isomorphism in ModuleCat k; its `_smul` law records
compatibility with the existing k-actions on both sides. An R-linear Ext
comparison is never promoted to k-linearity without proof.

## Concentration and the coefficient line

The residue Hom-complex theorem supplies vanishing in every integer
degree except two and length one in degree two. The actual injective
resolution supplies its K-injectivity, nonnegative term bound and original
quasi-isomorphic augmentation. Transport through the preceding k-module
isomorphism proves:

- `derivedResidueCoinduction_homology_isZero` for every integer n≠2;
- `derivedResidueCoefficientLine_length`, equal to one;
- `derivedResidueCoefficientLine_finite` and `_finitePresentation`;
- `derivedResidueCoefficientLine_finrank`, equal to one over k.

No basis or orientation is selected. The line is coherent as a finitely
presented module over k; its associated sheaf on Spec k has the same
ordinary finiteness consequence.

`derivedResidueCoinduction_isGE` and `_isLE` give concentration bounds on
the installed derived object. `derivedResidueCoinductionSingleIso` is
exactly the original `DerivedCategory.Plus.isoSingleHomology` comparison
with the degree-two single of the actual V. Its `_homology` theorem says
that the induced map on native H² is the identity after the installed
single/homology identification. Thus D_k≅V[-2] has its original homology
normalization and no selected identification V≅k.

## Remaining consumer boundary

This is the intrinsic residue coefficient needed for the surface-to-curve
normalization. It does not extend CM-curve concentration to coefficient V,
identify the surface's Cartier coefficient with the curve's chosen-embedding
coefficient, prove canonical field base change, or supply the global
Cartier/Serre counit identities. The ordinary evaluation-at-one counit and
the derived-resolution unit equations stated here are retained exactly;
no additional trace compatibility is claimed. These further map identities
remain genuine R.R3 and canonical-generation obligations.
