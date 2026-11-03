# Affine global-sections map formulas

Source: [Map.lean](Map.lean).

The public lemmas `moduleSpecΓFunctor_map_apply` and `moduleSpecΓFunctor_map_coe`
identify the actual native functor map with the same sheaf morphism on the top
open. They retain the original module carriers, scalar actions and maps.

This focused leaf imports Mathlib's native tilde construction. The existing
[additive-functor provider](../Sections.lean) retains its original source and
imports no map-formula extension. Consumers requiring these formulas import
this leaf directly.
