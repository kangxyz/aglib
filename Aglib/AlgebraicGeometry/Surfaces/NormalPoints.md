# Original singular points of normal surfaces

Source: [NormalPoints.lean](NormalPoints.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.NormalPoints`.
All four existing public names remain in `AlgebraicGeometry.Scheme`:

- `regular_at_of_normal_of_stalk_dimension_le_one`;
- `regular_at_nonclosed_of_normal_dimension_le_two`;
- `isClosed_singleton_of_singular_of_normal_dimension_le_two`;
- `stalk_dimension_eq_two_of_singular_of_normal_dimension_le_two`.

Their actual scheme is locally Noetherian and has normal stalks. The first
theorem requires the selected original stalk dimension at most one; the
remaining statements use scheme dimension at most two. The original local
ring is a field or DVR in the low-dimensional case, hence regular. Original
coheight and stalk dimension then make every actual singular point closed
with dimension exactly two.

These are the SAME four implementation bodies and public signatures formerly
owned by `Resolution/RationalDoublePoint/ClosedSingularPoints`. That file
publicly re-exports them and retains its complete-base finite-singular-set
consumer. No complete, Nagata, rational, integral, coefficient-field,
separatedness or global resolution premise is added to these generic facts.
The lower imports no RDP finite-locus or canonical theory.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/SingularAncestors](Resolution/NormalizedPointBlowupChain/SingularAncestors.md), [AlgebraicGeometry/Surfaces/Resolution/RationalDoublePoint/ClosedSingularPoints](Resolution/RationalDoublePoint/ClosedSingularPoints.md).
