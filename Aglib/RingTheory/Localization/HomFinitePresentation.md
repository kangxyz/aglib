# Native Hom localization with original monoid parents

`IsLocalizedModule.mapExtendScalars_of_finitePresentation` proves localization
of the **existing** `IsLocalizedModule.mapExtendScalars S f g D`, retaining the
supplied additive monoids, module actions, maps, scalar towers and localization
witnesses. Only the source of f must be finitely presented; no Noetherian,
finite-target or finite-dual premise is added. Module universes are independent.

The proof derives four additive groups with the native reducible
`Module.addCommMonoidToAddCommGroup`. Each extends its given additive monoid
and uses its existing ring action. These groups occur only inside the property
proof, which applies the native finite-presentation supplier once. The original
map, monoid parents and module structures in the statement are not replaced.

The actual affine-forms restriction consumer uses this law for the native first
dual localization map qd, then applies the original Hom restriction law again.
This focused leaf imports only `Mathlib.Algebra.Module.FinitePresentation`;
existing HomEvaluation and the stable sheaf/Hom suppliers are unchanged.
The exact supplier `e9043fad` passed the normal native owner check (own096, 2.1s).
The changed actual S1 consumer remains unaccepted; neither the earlier metadata
diagnostic nor this lower pass establishes its proof/kernel check.
