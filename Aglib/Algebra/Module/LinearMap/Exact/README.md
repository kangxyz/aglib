# Exact diagrams of original linear maps

[Diagram](Diagram.lean), imported as `Aglib.Algebra.Module.LinearMap.Exact.Diagram`, proves `LinearMap.bijective_of_rightExact_diagram`. Both rows use the displayed native linear maps and `Function.Exact`; their final arrows are surjective. The two original commuting squares, surjectivity of the first vertical map, and bijectivity of the middle vertical map imply bijectivity of the final map.

The ring is arbitrary and every one of the six module carriers has an independent universe. The direct element argument avoids any carrier resizing. No Noetherianity, finite generation or field hypothesis is required. The projective higher Serre pairing consumes this statement on its original Ext and dual-cohomology rows.
