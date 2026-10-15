# Subtype restriction of a dependent sum

Import `Aglib.LinearAlgebra.DFinsupp.Subtype`.

`DFinsupp.subtypeDomainLinearMap_surjective` proves surjectivity of the original
native restriction to a subtype. `DFinsupp.subtypeDomainLinearEquiv` upgrades
that same map to a linear equivalence when every omitted fiber is subsingleton.
Its application equation is the original coefficient restriction. The scalar
ring may be any semiring; neither index type needs to be finite.

The current consumer removes the zero proper-nonempty-support homology fibers
from the native Laurent weight coproduct. It retains the actual finite set of
empty- and full-support weights, rather than replacing the original complex.

The leaf was compiled independently through the shared serialized wrapper,
receipt `1792084878831320000-7642`.
