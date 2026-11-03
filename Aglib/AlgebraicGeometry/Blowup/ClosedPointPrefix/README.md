# Finite prefixes, rerooting and singular height

[Composite](Composite.lean) defines the endpoint-to-root map by finite
recursion on the original `ClosedPointPrefix` and proves its point equation.
[Reroot](Reroot.lean) separates the first actual child by one native sigma
equivalence; prepend, first-child fibres and truncation laws use that same
construction. Eligibility may be arbitrary, while the centres retain their
global closedness and nongenericity.

[Height](Height.lean) applies native König to the original truncation maps.
Finite parent fibres and absence of a compatible sequence imply an empty
level. The height is its least index, is positive, and strictly decreases
at actual children. [Height/Multiset](Height/Multiset.lean) uses the native
Dershowitz–Manna relation with multiplicities.

[BaseChange](BaseChange.lean) and
[Height/BaseChange](Height/BaseChange.lean) identify the original singular
prefixes and least heights under a flat preimmersion whose root image is
globally closed. They use the actual point-centre ideal equality, native
blowup Cartesian square and flat local regularity comparison.
Surface consumers must prove finite branching and the path contradiction
before using these interfaces for finite resolution.

Present consumers include [Normal stages and normalized presentation of ordinary chains](../../Surfaces/Resolution/PointBlowupChain/README.md), [Conditional resolution from original full quadratic cones](../../Surfaces/Resolution/RationalDoublePoint/README.md).
