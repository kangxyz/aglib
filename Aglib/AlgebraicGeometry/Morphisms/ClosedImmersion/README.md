# Noetherianity of closed sources

[Noetherian](Noetherian.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Noetherian`, proves that the source of an actual closed immersion is locally Noetherian when the target is, and Noetherian when the target is. The local and global hypotheses are separate statements; no regular-immersion or finite-dimensional assumption is added.

The actual geometric source/property transport supplies the scheme hypotheses used by [coherent closed-immersion direct image](../../Modules/Coherent/Pushforward/ClosedImmersion/README.md). Affine quotient-ring pushforward and coherent exactness are later module-theoretic interfaces.

The Noetherian source lemmas depend directly on native Mathlib Noetherian and closed-immersion theory, below the module-sheaf direct-image construction.

[Spec](Spec.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Spec`, proves `IsClosedImmersion.surjective_of_specMap` for the actual ring map of a closed spectral morphism. No Noetherian, ideal-module or smoothness premise is added.
