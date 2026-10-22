# Local colength in a regular parameter chart

`Colength.lean` uses the literal `Localization.Away.saturatedChart` and the
`weakTransform` ideal constructed in `WeakTransform.lean`. Its local consumer
is the termination input for principalizing a finite-colength ideal on a
regular surface.

The parameter-power results assume `a` is regular on `A` and `b` is regular
on `A/(a)`. They prove `(a,b)^(n+1) : a = (a,b)^n`, then contract every
exceptional power in the actual saturated chart back to `(a,b)^n`.
`exists_unique_parameter_order` constructs the actual finite order from a
power containment `(a,b)^N ≤ J` and properness of `(a,b)`.
`exists_positive_parameter_order` adds positivity from `J ≤ (a,b)` and
returns the proved upper bound and maximality.

For a Noetherian base and maximal parameter ideal, the actual-order weak
transform has an Artinian chart quotient, finite support consisting of
maximal ideals, and finite length in each actual prime-localized quotient.
`Ideal.quotientAtPrime` is a transparent abbreviation of
`Localization.AtPrime P / K.map algebraMap`.

`chartPowerDivision` is the A-linear map obtained by dividing an element of
the original centre-ideal power by the actual exceptional power.
`weakTransformDivision` composes it with the actual quotient map.
A parameter-ideal element of order at least `r` has a polynomial presentation
of degree at most `r` in the literal chart ratio. At the actual ideal order,
this supplies a nonzero initial polynomial of degree at most `r` on the
original polynomial exceptional fibre. Polynomial division gives surjectivity
modulo the exceptional parameter; its nilpotence lifts this to surjectivity
of `weakTransformDivision`.

`weakTransform_colength_lt` compares that quotient with the proper image of
`(a,b)^r` in the original finite-length module `A/J`.
`weakTransform_local_colength_lt` transfers the strict inequality to the
actual prime localization, and `weakTransform_local_colength_toNat_lt`
expresses it as a strict decrease of natural numbers. The hypotheses retain
the positive actual order, both ideal-power containments, and finite length
of the original quotient. The order-existence results supply the exponent
conditions from the original parameter-ideal data.

The native results here concern individual chart and local colengths. Their
[finite point-blowup principalization consumer](../../AlgebraicGeometry/Surfaces/Resolution/Principalization.md)
now constructs the actual finite chain and proves the original Cartier
pullback for a nonzero ideal with Artinian quotient on a locally Noetherian
regular integral scheme of dimension at most two. The sharper triangular and
residue-degree-weighted defect formula and the full graph-to-ideal
construction for common regular domination are not formalized here. This
module uses the regular-pair chart and fibre comparisons and is independent
of the exceptional normal-line calculation.
