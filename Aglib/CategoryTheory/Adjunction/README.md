# Actual adjunction hom-equivalences

[MateHomEquiv](MateHomEquiv.lean), imported as `Aglib.CategoryTheory.Adjunction.MateHomEquiv`, gives `CategoryTheory.homEquiv_conjugate` and `homEquiv_to_identity`. They compare the actual adjunction hom-equivalence after the supplied natural isomorphisms, retaining the original unit/counit maps.

These generic categorical equations support scheme tensor/pushforward and projection-formula mates. They contain no scheme, flatness, finiteness or cohomology assumption; those belong to the geometric consumers of the comparison.

[MateHomEquiv](MateHomEquiv.lean) retains original mate hom-set transposition. [Mates](Mates.lean) adds the actual four-adjunction comparison/unit identity and conjugate/mate whiskering transport, with independent category universes and explicit isomorphism conditions preserved.
