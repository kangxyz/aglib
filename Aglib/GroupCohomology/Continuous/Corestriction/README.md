# Continuous finite-open corestriction

[Sections](Sections.lean) owns actual coset sections and one implementation of
finite transfer in degrees zero, one and two. The subgroup is open and has
finite index. Openness makes the actual coset quotient discrete, so each
representative section is continuous; the coefficient topology remains the
supplied topological additive-group topology.

[Basic](Basic.lean) specializes these maps to `CosetSection.chosen`, whose
representative is the original quotient `out`. The default transfer and H1/H2
maps abbreviate this same general implementation. The native continuous H1
carrier and the H2 cocycle quotient are retained.

[ProjectionFormula](ProjectionFormula.lean) proves the continuous cup projection
formula from the actual pairing. Its finite-sum continuous primitive gives the
cocycle equality up to the native bar boundary before descending to H2.
[Tower](Tower.lean) supplies explicit section-change primitives, section
independence on H1 and H2, the actual nested-subgroup identification and finite
open tower transitivity. The nested H1 maps delegate to native H1 restriction.
The subgroup inclusion, openness, finite-index assumptions and coefficient
actions remain explicit. No norm or transfer-transitivity assertion is an input.
