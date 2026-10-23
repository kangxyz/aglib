# Original structure comparisons for proper birational morphisms

The premises are integral source and target, an actual proper dominant
morphism, target `NormalStalks`, and invertibility of the original
`functionFieldMap`. No Noetherianity or dimension bound is imposed.

`Hom.bijective_structuralCoefficients_of_isProper_birational` specializes to
an affine target `Spec R` and proves bijectivity of exactly

```lean
f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
```

It uses the existing affine-open birational-functions theorem at the whole
target and the original `ΓSpecIso`. The integrality and common-function-field
argument remains in `Morphisms/Proper/BirationalFunctions.lean`.

`Modules.isIso_unitToPushforwardObjUnit_of_isProper_birational` proves
invertibility of the original structure-module map
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom` from the existing
`IsIso f.c`, component by component. The theorem
`Modules.isIso_pullbackPushforwardAdjunction_unit_unit_of_isProper_birational`
then proves invertibility of the original pullback/pushforward adjunction
unit on the target structure module. The native `pullbackUnitIso_homEquiv`
retains the actual equation connecting these two maps.

`Cohomology.moduleH0LinearEquivOfProperBirational` gives an `R`-linear
equivalence from `R` to the original degree-zero structure-module `Sheaf.H`,
using its unchanged structural action. Its `_sections` formula sends a
scalar `r`, through `moduleH0EquivOfHom`, to the literal section
`f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)`.

These results supply the degree-zero and ordinary-unit comparisons.
Cohomological dimension, higher derived-unit statements, Leray exactness,
and puncture injectivity remain separate obligations.
