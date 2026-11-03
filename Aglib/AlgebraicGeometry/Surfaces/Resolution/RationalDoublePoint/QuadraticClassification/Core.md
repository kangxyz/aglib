# Classification on the actual full quadratic cone

API: [exceptional_original_quadratic_alternatives_of_quadratic_kernel](Core.lean#L37), [exceptional_original_quadratic_alternatives_of_hilbert](Core.lean#L104).

`Core.lean` contains the single square/nonsquare split formerly in the
inverse-line cohomology consumer. Its weakest input is the actual original
three generators and a nonzero homogeneous quadratic generating the entire
original canonical cone kernel, together with the genuine normal rational
surface hypotheses needed for chart normality and the actual cubic.

Existing denominator, dehomogenization and presentation laws derive the
original affine-chart presentation; no new cone or polynomial backend is
introduced. Case I retains the global homogeneous nonsquare condition as well
as its selected-chart consequence. Case II normalizes the actual generators
and constructs a true original cubic with nonzero residue, in every
characteristic, without a coefficient-field section or square roots.

The Hilbert-function sibling merely invokes the existing full-kernel producer
on the displayed original generators, then calls that same split. The old
inverse-cohomology theorem is a thin caller above it with unchanged public
telescope. This separation lets initial actual cone data and genuinely
computed later Hilbert data use one implementation without requiring initial
Hilbert data in a path theorem or reintroducing later inverse-line cohomology.

This is an intermediate classification boundary, not a final-resolution
certificate: a final path theorem must produce its later Hilbert functions
from the actual child geometry, rather than assume future cones or markers.

The base is a commutative normal Noetherian Nagata local domain of
dimension two with `NormalModificationH1Vanishing` and nonregularity.
`exceptional_original_quadratic_alternatives_of_quadratic_kernel` consumes
the displayed generating triple and full nonzero homogeneous quadratic.
`exceptional_original_quadratic_alternatives_of_hilbert` instead consumes
the complete Hilbert function on those generators and calls the same split.

Present consumers: [OriginalPathCones](../OriginalPathCones.md), [QuadraticClassification](../QuadraticClassification.md).
