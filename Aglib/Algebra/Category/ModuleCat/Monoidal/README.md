# Scalar restriction's tensor comparison

[RestrictScalars](RestrictScalars.lean), imported as `Aglib.Algebra.Category.ModuleCat.Monoidal.RestrictScalars`, supplies `ModuleCat.isIso_restrictScalars_tensor`. For commutative rings and a ring equivalence, the original lax-monoidal scalar-restriction tensor map is invertible on the actual target modules.

The forward map and pure-tensor normalization are Mathlib's existing lax-monoidal restriction map. The ring-equivalence premise matters; no strong-monoidal conclusion is asserted for an arbitrary scalar map. Presheaf tensor pushforward and stalk coefficient comparisons consume this lower interface.
