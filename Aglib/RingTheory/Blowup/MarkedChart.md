# The original marked saturated chart

Import `Aglib.RingTheory.Blowup.MarkedChart`.
The consumer is the corrected Case-II chart argument that must construct
the marking used by `AlgebraicGeometry.Blowup.Arc.MarkedPath`.

`localizedChartMap` is the original coefficient map from `A` to the
localization at the specified prime of the literal native saturated chart
`A[I/a]`. `localizedChartMap_center` derives the full ideal equality
`map I = (a)` for that same original map and element. It uses the existing
chart ideal equality followed by the original localization map.

`saturatedChart_isNoetherian` derives Noetherianity from the finite actual
fraction generators of the original ideal. The selected prime localization
therefore has its native Noetherian local-ring structure.

`first_not_mem_sq_of_span_triple_of_not_regular` proves that the first of
three displayed maximal-ideal generators cannot belong to the maximal-ideal
square in a singular local ring of dimension two. If it did, Nakayama would
remove that generator, leaving two generators and forcing regularity.
No normality, domain, residue characteristic or tangent equation is needed
for this particular implication.

At the actual generic double-line stalk, `isUnit_of_generic_double_line_relation`
uses its DVR structure, `m = (t,v)`, `v` outside `(t)`, and `v² = t*a` to
derive that `a` is a unit. Total divisibility gives `t = v*b`; nonmembership
forces `b` to be a nonunit, hence a multiple of `v`. Cancellation in the
domain then proves that `a` has an inverse.
`isUnit_cubic_coefficient_of_generic_double_line` applies this to the actual
transformed relation `v² + t*H + t*v*l + t²*r = 0` and proves that `H` has
nonzero generic residue. A single true relation suffices; no equality with
an ambient hypersurface presentation, coefficient field, or numerical
valuation is required. Producing the stated generic DVR and quotient data
from the normal ordinary blowup remains the geometric input.

`localizedChart_parameter_not_mem_sq` applies that argument to the actual
prime ideal displayed as `(a, s/a - alpha, z/a)` in the original saturated
chart. The prime equality, dimension two and singularity are explicit
inputs. The maximal ideal after localization and minimality of the same
exceptional element are conclusions.

An actual point homomorphism from the chart to the original residue field
with the original coefficient equation gives a second part of the marking.
`localizedChartMap_isLocal_of_residue_point` proves locality of the original
map to its actual prime localization. `localizedChartMap_residue_bijective`
derives bijectivity of that map's residue-field map. The point is surjective
because its coefficient composite is the original residue quotient; the
native localization residue equivalence retains those same coefficients.
No coefficient field, residue section, complete DVR, arc or terminating
chain is supplied.

The mathematical basis is the corrected Case-II tail paper
`rdptail-correction.md`, SHA-256
`b8af2ac963fdd35e65f98b00641ba4be2a200bed0521e5a1ffc1d337fa859e40`,
especially its original chart convention and marked continuation argument.

The remaining corrected-RDP obligation is to produce the actual rational
point and displayed prime from the tangent-square and repeated-root
criterion, and prove persistence of the simple-root binary-cubic marker.
Normality of the actual blowup is used there to show that the binary cubic
is nonzero. This file does not derive normality, dimension, the tangent
equation, or the marking's global existence, and concludes no RDP or RES
closure.
