# Cohomology of projective curves with a coefficient line

The coefficient Serre and generation interfaces use the actual closed
projective embedding over an arbitrary field, positive ambient dimension,
the closed-stalk regular-primary parameter condition and a finite
rank-one coefficient module `V`. The line `V` remains explicit.

[Generation](Generation.lean) identifies the degree-zero Serre Hom–H1
pairing by its original trace formula and proves absence of coherent
finite-support subobjects, also after tensoring by an invertible line.
[TwistVanishing](TwistVanishing.lean) proves H1 vanishing for the coefficient
canonical sheaf tensored with a globally generated nontrivial line, when
the original structural H0 map is bijective.

[AnticanonicalHilbert](AnticanonicalHilbert.lean) computes powers of the
dual ideal of an actual finite Cartier divisor from the stated unit and
ideal cohomology, or the full divisor H0 rank. Properness and CM hypotheses
are unnecessary once that finite Cartier datum is supplied.
The [hyperplane-power family](AnticanonicalHilbert/README.md) constructs
the needed numerical inputs on the full projective curve.
[FieldExtension](FieldExtension.lean) retains the original closed parameters
under the stated flat integral base change.
The [section and generation family](Generation/README.md) records its
remaining generation inputs separately.

Present consumers include [Canonical coefficients on embedded normal surfaces](../NormalSurface/README.md), [Conditional resolution from original full quadratic cones](../../../../../Surfaces/Resolution/RationalDoublePoint/README.md).
