# Finite-etale monodromy

`Coefficients` and `PointedCharacters` relate the actual fibre action,
coefficient marking and pointed characters. Their native owners are the
corresponding `Scheme.FiniteEtale` namespaces and the generic
`GroupCohomology.PrimitiveCharacters.Translation` interfaces they extend.

These leaves consume the actual finite-etale group-scheme and generic
continuous-character constructions. The chosen point, coefficient level,
marking, continuity, exact-order and classification inputs remain those in each
theorem. Surjectivity/transitivity conclusions do not manufacture an absent
GC/FF dictionary. Current consumers are group-scheme monodromy and finite H1
comparison; specialized curve and arithmetic realizations remain downstream.
