# One original power-relation presentation

Source: [PowerRelation.lean](PowerRelation.lean).

`IsAdjoinRootMonic.ofPowerRelation` starts with normal domain A, domain
A-algebra B whose scalar action is torsion-free, a specified generator z, a
nonzero natural p, actual `finrank A B = p`, `algebraMap A B a = z^p`, and
`Algebra.adjoin A {z} = top`. It presents that same B by `X^p-C a`.

The constructor is the native minimal-polynomial presentation of z. Its
power-basis rank, the original power relation, and monicity identify the
polynomial. `ofPowerRelation_root` retains exactly z, and
`ofPowerRelation_map` retains exactly `Polynomial.aeval z`.

No prime-degree, characteristic, local-ring, Noetherian, or module-finite
premise is added. Integrality of the specified generator is derived directly
from its positive power relation by native `IsIntegral.of_pow`; no separate
integrality premise or module-finiteness premise survives in this constructor.

This one body replaces the previous private construction in
`DiscreteValuationRing/PureDegreeP/Monogenic` and the duplicate field construction
in `Kaehler/PureDegreePTrace/Field`. The integral-generator entrance also uses
this body; it does not introduce a third backend.

Direct consumers: [RingTheory/DiscreteValuationRing/PureDegreeP/Monogenic](../DiscreteValuationRing/PureDegreeP/Monogenic.md), [RingTheory/IntegralClosure/PureDegreePGenerator](../IntegralClosure/PureDegreePGenerator.md), [RingTheory/Kaehler/PureDegreePTrace/Field](../Kaehler/PureDegreePTrace/Field.md).
