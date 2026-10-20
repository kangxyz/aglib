# Continuous second cohomology and cup cocycles

The parent leaf `Aglib.GroupCohomology.H2.Continuous` owns
`GroupCohomology.H2.Continuous`. Its `Cocycle` is the actual additive subgroup
of bundled continuous maps `G × G → A` satisfying the inhomogeneous bar
identity. `Group` is its quotient by the bar differential, implemented through
the existing four-term multiplication-cone data. `classOf` retains that actual
quotient map. The degree-zero differential uses the existing native continuous
H1 principal cocycle, and closed one-cochains return that same H1 cocycle type.

The topological group and topological additive coefficients carry their supplied
jointly continuous additive action. No discrete coefficient topology is added.
The smart truncation uses genuine two-cocycles and a zero final differential;
it does not construct a separate H1 carrier.

[Cup](Cup.lean) supplies an actual bilinear, continuous, equivariant `Pairing`
and its continuous cup two-cocycle. Subgroup restriction delegates to the native
continuous H1 restriction and its inherited action. [CupBilinear](CupBilinear.lean)
proves bilinearity of the cocycle/class maps for a pairing `A × A → C` and gives
explicit continuous primitives when either one-cocycle is principal. The
coefficient groups are arbitrary, despite historical application notation.

Finite-open-subgroup transfer and its explicit cup projection primitive live
in the sibling continuous corestriction family.
