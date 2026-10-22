# Artinian quotient subschemes from actual stalk ideals

Import `Aglib.AlgebraicGeometry.IdealSheaf.Artinian`.

All declarations are in `AlgebraicGeometry.Scheme.IdealSheafData`. `stalkIdeal_subschemeι_eq_ker_stalkMap` identifies the original ideal stalk at a point of its actual quotient subscheme with the kernel of that original closed-immersion stalk map. It has no Noetherian premise.

`isLocallyArtinian_subscheme_of_stalkQuotient_finiteLength` assumes a locally Noetherian ambient scheme and finite length of every actual quotient `O_X,x / J.stalkIdeal x`. The original surjective stalk map identifies that quotient ring with the quotient-scheme stalk. Its Artinianness gives dimension zero, and the native dimension equality proves local Artinianness of the actual quotient scheme.

`isArtinian_subscheme_of_finite_support_of_stalkQuotient_finiteLength` adds finite support. The original closed immersion identifies its point set with that support, supplying compactness. On a Noetherian ambient scheme, callers may instead use the original closed immersion's quasi-compactness to obtain compactness, then combine it with the local-Artinian theorem.

These three proofs were moved from the initial principalization producer into this lower owner for the resolution and rational base-ideal consumers. Their actual objects, maps, universes, local Noetherianity and finite-length guards are retained. No blowup or surface source is imported, and no global principalization theorem is assumed.
