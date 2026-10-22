# The weak ideal on the actual point blowup

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.WeakTransform`.

For a native ideal sheaf I on a locally Noetherian scheme and its actual universal blowup B, `BlowupDatum.weakTransform B J r` is `(J.comap B.map).colon ((I.comap B.map)^r)`. The quotient is constructed on the affine basis by the localization-compatible ideal-sheaf quotient supplier. Its affine and actual-stalk equations retain the original ideals, morphisms and exponent.

If J is contained in I^r, `exceptional_pow_mul_weakTransform` proves the exact equality `(I O_B)^r * W = J O_B`. The proof uses the actual local regular generators supplied by B.cartier and equality in the original stalks. `chart_weakTransform_eq_affineCenter` identifies W on every literal saturated affine chart with the ring-theoretic weakTransform already used by the strict colength theorem.

For an actual closed point x, `pointCentre_stalkIdeal` identifies the original point ideal at x with the maximal ideal of the original local ring; it is the unit ideal elsewhere. Thus `le_pointCentre_pow_iff` derives global containment from the original local containment. `exists_positive_pointCentre_order` uses the actual regular parameters and finite local colength to construct the positive order, with noncontainment in the next power.

`pointBlowupComparison_comap_weakTransform` uses the same actual local-spectrum blowup comparison as the regularity supplier. Its stalk maps are isomorphisms by flatness and surjectivity on stalks, so the original global weak ideal pulls back to the weak ideal of the original maximal ideal and original stalk ideal.

An actual Artinian quotient subscheme gives finite support consisting of closed points. Local Artinianness gives Artinian original stalk quotients; with a locally Noetherian ambient scheme these have finite length. These are consequences of the original ideal sheaf and its quotient subscheme, not additional transform data.

[Finite point-blowup principalization](Principalization.md) now constructs a finite chain of the actual point blowups for a nonzero ideal with Artinian quotient on a locally Noetherian regular integral scheme of dimension at most two, and proves the original pulled-back ideal Cartier. It uses finite support, strict local colength decrease and well-founded multiset recursion; no decrease of the unweighted sum is asserted. Nonzero ideals at stalks of dimension at most one are already Cartier. Arbitrary divisorial-part removal and the rational-map/common-domination bridges remain beyond this result. No normal-bundle formula, excellence, perfectness or algebraically closed residue field is assumed.
