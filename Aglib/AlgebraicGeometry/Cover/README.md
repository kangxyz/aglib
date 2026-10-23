# Binary affine covers

| Source | Reusable interface |
| --- | --- |
| [AffineBinary](AffineBinary.lean) | An actual affine binary open cover, retaining its two opens and their overlap. |
| [AffineBinary/Limit](AffineBinary/Limit.lean) | Both original opens and their affine intersection descend to a stage of a qcqs inverse limit with affine transitions, with their actual recovery equalities. |

These are the cover inputs used by the invertible-sheaf lifting and proper
finite-presentation model interfaces. The cover is an explicit hypothesis; it
is not inferred from properness alone.
