# Source-ring action on native ambient Ext

`coinducedExtSourceModule q N n` is an explicit, non-global module
structure over `S` on native `Ext_R^n(Res_q S,N)`. It is transported from
the existing higher coinduction comparison, without introducing another
Ext carrier or requiring an `S`-action on `N`.

`coinducedExtSourceModule_smul` identifies every scalar with original
Yoneda precomposition by restricted right multiplication on `S`.
`coinducedExtSourceModule_map_smul` proves that `q(r)` acts by the
unchanged ambient `R`-scalar action. These statements require no
surjectivity of `q`.

`derivedCoextendScalarsPlusHomologyExtSourceLinearEquiv` upgrades the
unchanged installed derived-homology comparison to an `S`-linear
equivalence, for any supplied injective resolution. Derived-category
sizes and Ext size remain independent. Geometric stalk comparisons may
use the scalar compatibility and actual surjectivity of their stalk map
to upgrade their original ambient-linear maps.
