# Closed scheme points

[Closed](Closed.lean) defines `Scheme.ClosedPoint X` as the actual points of
`X` whose singleton is closed. It carries no curve or Noetherian hypothesis.
Finite-morphism fibre and residue-field consumers use this same subtype.
The source is the frozen R5 packet, with the exact hash recorded in the leaf.
