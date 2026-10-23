# Original ideal-module stalks

`Scheme.Hom.idealModuleStalkEquiv i x` identifies the native module stalk of
the original kernel module `idealModule i` with the ideal
`i.ker.stalkIdeal x` in the original local ring `X.presheaf.stalk x`.
The hypothesis is `[QuasiCompact i]`; every closed immersion satisfies it.
No Noetherianity, normality, regularity or rank assumption is used.

The comparison is constructed from `idealInclusion i`. The preliminary
`Scheme.Modules.unitModuleStalkAddIso` is the canonical filtered-colimit
comparison for the composite forgetful functor from commutative rings to
rings to additive groups. Its refinement `unitModuleStalkEquiv` is linear
for Mathlib's native stalk-ring action. Both comparisons preserve the
original germs, by `unitModuleStalkAddIso_germ` and
`unitModuleStalkEquiv_germ`.

`idealModuleStalkInclusion` is the original inclusion on module stalks,
followed by that canonical unit-stalk comparison. It is injective because
the native module-stalk functor preserves monomorphisms. Its image equals
`i.ker.stalkIdeal x`: every ideal-module germ can be represented on an affine
neighbourhood, and every affine kernel element lifts through the original
`idealSectionsEquiv`. Quasi-compactness is used exactly in the native
`Scheme.Hom.ker_apply` identification on affine opens.

`idealModuleStalkEquiv_val` retains the original inclusion, and
`idealModuleStalkEquiv_germ_val` sends the germ of a section to the original
structure-sheaf germ of its inclusion. The result does not choose a different
line module or assume a comparison with the stalk ideal.

The current consumer is
`Aglib.AlgebraicGeometry.IdealSheaf.Cartier.SectionFibres`. The original
objects are supplied by `IdealSheaf.Modules`, `IdealSheaf.Colon` and
`Modules.Stalk.Basic`, with Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean 4.34.1.
