# Original open-restriction kernels and actual extensions

`Scheme.Cohomology.exists_extension_retraction_of_structureRestriction_eq_zero`
applies to any scheme `X` and actual open `U`. The input is a class in
`Sheaf.H (moduleAddSheaf X O_X) 1` killed by
`moduleCohomologyMapAlong U.ι (Scheme.Hom.structureModuleMap U.ι) 1`.
There is no properness, normality, dimension or Nagata premise.

It constructs an actual short exact extension of `O_X` by `O_X`, its
original class equation under `moduleExtCohomologyMap`, and an actual map
`rU : E.middle.over U → O_X.over U` with
`(overFunctor X.ringCatSheaf U).map E.i ≫ rU = identity`.
This is the retraction used by the original complementary-section
construction.

The native `moduleExtCohomologyAddEquiv` and `Ext1.exists_extension`
realize the class. The exact original restriction equation from
[Restriction](Restriction.lean) identifies its restricted Ext class.
`restrictUnitIso_hom_adjoint` retains the structural coefficient map;
its canonical inverse cancels the unit normalization on Ext. Thus the
actual restricted extension class is zero.

`ShortComplex.ShortExact.extClass_eq_zero_iff_splitting` supplies the
splitting criterion on the same short complex. In the zero-class
direction, the native covariant Ext exact sequence lifts the identity
through degree zero; `Ext.mk₀_bijective` makes that lift an actual section
of the quotient. Exactness gives the full splitting. A splitting makes
the class zero through its original section and `comp_extClass`.

Finally `overFunctorEquiv U` and the fully faithful `overEquiv U` transport
the restricted retraction to the original over-site. Its identity follows
from the naturality square and the original retraction equation. No
splitting of the original extension over all of `X` is assumed.

The [surface graph consumer](../../../Surfaces/Resolution/ExtensionGraph/Construction.md)
uses this construction on the literal inverse image of the punctured
spectrum. This module does not supply graph normalization, the Nagata
chart theorem, or surface resolution.
