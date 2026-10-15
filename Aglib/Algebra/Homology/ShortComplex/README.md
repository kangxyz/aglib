# Short exactness of retract diagrams

[Retract](Retract.lean), imported as `Aglib.Algebra.Homology.ShortComplex.Retract`, gives `CategoryTheory.ShortComplex.shortExact_of_retract`. In the stated abelian setting, an actual retract of a short exact short complex is short exact. The supplied retraction is in the short-complex category, so its maps preserve the diagram.

This generic result is below finite-free tensor retracts and scalar/sheaf exactness arguments. A degreewise split morphism of cochain complexes is a different interface and does not by itself supply this chain-level retraction data.
