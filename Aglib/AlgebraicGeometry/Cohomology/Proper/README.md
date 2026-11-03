# Proper cohomology with original structural coefficients

[FibreIdempotents](FibreIdempotents.lean) maps the ordinary pushforward
stalk to sections of the literal scheme-theoretic fibre and retains the
original germ and residue-constant triangles. It does not assert that
every fibre idempotent lifts through that map.

[FiniteExtension](FiniteExtension.lean) transfers a uniform original
structure-H1 length bound along a finite faithful local algebra of normal
Noetherian Nagata domains of dimension two, with separability of the
original function-field map. This boundedness predicate is not resolution
existence or universal vanishing.

[GrauertRiemenschneider](GrauertRiemenschneider.lean) proves H1 vanishing
of the canonical module of a supplied finite-coordinate projective
embedding over a dimension-two regular local domain. The target base is
a complete Noetherian normal local surface, with an actual finite injective
local map from that regular base; the original proper birational normal
model and structural triangle are retained.
[CanonicalTraceAnnihilator](CanonicalTraceAnnihilator.lean) turns an
original trace-image condition on that same coinduced coefficient into
annihilation of original structure H1. It does not produce the trace-image
condition or its later nonzero uniform annihilator.

The [derived structure family](DerivedStructure/README.md) records the
separate finite-length, supported-R1 and derived-unit implications.

Present consumers include [Proper graph closures and Chow modifications](../../Morphisms/Proper/README.md).
