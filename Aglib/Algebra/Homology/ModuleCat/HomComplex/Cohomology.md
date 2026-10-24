# Original Hom cohomology, derived morphisms and Ext

[Cohomology.lean](Cohomology.lean) compares the homology of the actual
module-valued Hom complex with original morphisms in the derived category.
The coefficient complex is explicitly K-injective. The comparison first
uses the native forgetful homology isomorphism, then the identity comparison
with additive Hom cochains, then the native cocycle and localization maps.
It preserves precomposition by the original source chain map.

`moduleHomologyClassesNatIso` assembles those same three comparisons as a
natural isomorphism from native module Hom homology to `cohomologyClassFunctor`.
The latter functor uses the original `cohomologyPrecomp` in every map.
`moduleHomologyClassesAddEquiv` is the component of that complete comparison.
Its forward equation identifies it with the original class isomorphism.
`ModuleCat.natIsoAddEquiv` and `ModuleCat.natIsoAddEquivTrans` retain the full
functor and natural-isomorphism arguments. Their generic naturality is used
inside `ModuleCat.natIsoAddEquivTransLinear`, before the concrete homology
objects are supplied. The public categorical naturality theorem and the
native class-to-derived precomposition law retain the original source maps.

`moduleHomologyDerivedLinearEquiv` is linear for the existing module
structure on homology. The generic construction uses the actual linear
homology functor and class-to-derived precomposition by `r • id`; no new
action is transferred to the source. `moduleCocycleClass` and
`moduleHomologyDerivedLinearEquiv_cocycle` identify the class of each actual
cocycle with `Q.map` of its native shifted chain map.

For an actual quasi-isomorphism `u : N[0] → J`,
`singleHomologyExtLinearEquiv` computes native `Ext M N n`. Its displayed
cocycle formula uses the original source-single comparison, the localized
cocycle, and the inverse of `coefficientShiftIso N J u n`. Thus the original
augmentation and the native shift convention remain fixed. In particular,
`singleFunctor n` places a module in degree `n`; it is not a positive shift.
The module carrier universe and the derived-category and Ext sizes remain
explicit and independent.

For a ring map `sigma : R →+* A`, `coinducedSingleComplexIso` uses the
published evaluation-at-one coinduction isomorphism and the inverse native
source-single comparison. `coinducedSingleHomologyIso` then uses the original
exact restriction-of-scalars homology comparison. The resulting
`coinducedSingleHomologyExtLinearEquiv` is R-linear, starts from homology
with its intrinsic A-module structure, and computes the original R-Ext.
The source A-action is the actual source multiplication retained by
[Coinduction.lean](Coinduction.lean); no A-action is assigned to an arbitrary
R-coefficient module. The published component equations in that file are
available by their names for explicit rewriting.

Current consumers are the finite-length residue-line comparison and the
original two-layer Postnikov argument. Those require their own finite-length,
model, shift and geometric inputs. This module does not identify a surface
canonical sheaf, supply its concentration, identify the geometric trace,
or prove GR or B7 boundedness.
