# Original derived Hom comparison with the intrinsic residue line

[HomComparison.lean](HomComparison.lean) constructs the finite-leg comparison
for an actual finite local algebra `R → k`, where `R` is regular local of
dimension two and `k` is any field. The coefficient `V` is literally
`ModuleCat.derivedResidueCoefficientLine R k`, the own degree-two homology of
the installed right-derived coinduction of `R[0]`. No orientation `V ≅ k` is
chosen. The map `R → k` need not be onto, and its residue extension need not be
separable. Module carriers have the same universe as in the residue supplier;
the two derived-category universes may differ.

`residueLineHomEquivPlus` has an actual bounded-below derived `k`-module `M` as
source. Its left side uses the installed
`(restrictScalars (algebraMap R k)).rightDerivedFunctorPlus`, viewed in the full
derived category. Its right side uses the same original `M` and the original
single of `V`. For every integer `r` it gives the additive equivalence

```
Hom_R(Res M, R[0][r + 1]) ≃+ Hom_k(M, V[0][r - 1]).
```

The underlying `residueLineHomEquiv` uses the native exact restriction functor
on the full derived categories. Its source may in fact be arbitrary: only the
fixed target and its coinduced resolution must be K-injective. The bounded-below
adapter uses the existing `rightDerivedFunctorPlusCompιIso`; its explicit unit
law is retained by `residueDerivedRestrictionIso_unit`. This is the comparison
needed after `moduleDerivedGlobalSectionsRestrictIso`, without any claim about
an ordinary finite-pushforward right adjoint on all module sheaves.

The construction starts from the original injective resolution of the actual
module `R`. The native localization source model and exact-restriction
factorization enter `residueDerivedHomEquiv`. Its forward and inverse model
equations display the original `cochainDerivedHomEquivOfInjectiveResolution`,
the resolution inclusion, and the original installed right-derived model
comparison. K-injectivity is supplied by the existing injective-resolution
adjunction theorem, not imposed on the source. The native source-model choice
cancels from `residueDerivedHomEquiv_symm_eq_map_counit`.

`residueRightDerivedResolutionIso_eq` identifies the model comparison with the
same `derivedResidueResolutionIso` whose original augmentation/unit law is
proved in the parent file. `residueDerivedCounit` is the original resolution
counit of the restriction/coinduction adjunction. Its degreewise functional
formula evaluates at `1`. Each integer degree uses a shift of this same
counit, through the native `CommShift` comparisons.

`residueLineShiftIso` applies the already proved own-homology reconstruction,
whose map on degree-two homology is the identity after the installed single
normalization. The native single shift gives `D_k[2] ≅ V[0]`. The original
degree-two map `residueLineTrace : Res(V[0]) → R[0][2]` is the adjoint of its
inverse. It is a derived map, not an ordinary field trace. The inverse of every
line-valued Hom comparison is exact restriction followed by this same trace,
using original shifted composition. This proves the degree ledger
`2 + (r - 1) = r + 1` without natural-number truncation.

`residueLineHomEquiv_comp` and its inverse version preserve arbitrary shifted
derived-source composition. This includes the graded source action required
by the Serre/Yoneda consumer, rather than only degree-zero naturality.
`residueLineHomEquivPlus_symm_comp` retains the installed bounded-below source
and its original shift comparisons. The scalar laws explicitly identify
native `k`-scalar multiplication on the right with precomposition by the
original `a • 𝟙 M` after derived restriction on the left. No field action on the
left is manufactured by transporting through an arbitrary equivalence.

The original source-naturality law can be applied to the actual structural
`k[0] → RΓ_k(E, O_E)` to evaluate the line-valued trace. The geometric
restriction comparison and that actual structural map remain the caller's
existing objects. This leaf does not construct the surface/curve Serre
composite, Cartier purity, closed-stalk monicity, the coherent Yoneda
isomorphism, canonical generation, or an RDP/RES theorem.
