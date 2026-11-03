# Two-chart coverage and original child-prime parameters

API: [not_mem_squareChart_of_closed_exceptional_point](CaseTwoPoints.lean#L119), [mem_planeChart_or_opposite_of_closed_exceptional_point](CaseTwoPoints.lean#L142), [exists_actual_prime_parameter_at_closed_singular_point](CaseTwoPoints.lean#L158).

Let `A` be a commutative Noetherian local domain and
`B : BlowupDatum (affineCenter A (maximalIdeal A))`.
Take `t,s,z ∈ maximalIdeal A` generating that ideal, with
`doubleLineChildCotangentKernel A ![s,z,t] = Ideal.span {(X 1)^2}`.
The polynomial coefficients are in the original `ResidueField A`.

`not_mem_squareChart_of_closed_exceptional_point` excludes the square
coordinate chart for a globally closed point over `closedPoint A`.
`mem_planeChart_or_opposite_of_closed_exceptional_point` then places that
same point in `CaseOneChart.chart B t` or `CaseOneChart.chart B s`.
All three chart maps use the original `affineAtlas B`.
The proof permutes the given full kernel: the square chart's dehomogenized
equation is one and cannot lie in a plane maximal ideal.

For a singular point in the t-chart and a supplied `F : CubicRelation t s z`,
`exists_actual_prime_parameter_at_closed_singular_point` constructs the
original chart prime `P`, a monic irreducible polynomial `q` over the
original residue field, and its chart lift `Q`. With
`E := DoubleLinePresentation.ofKernel t s z hgen hker` and
`S := saturatedChart A (maximalIdeal A) (t : A)`, it retains

- `P = (Ideal.span {q}).comap E.reduction` and `E.reduction Q = q`;
- membership of the original exceptional parameter in `P`;
- the equation identifying the chart point with the supplied scheme point;
- dimension two and nonregularity of `Localization.AtPrime P`; and
- the native stalk isomorphism `ε` with
  `ε.hom.hom.comp (B.map.stalkScalar x) =
    localizedChartMap (maximalIdeal A) (t : A) P`.

The full parent kernel gives `t ≠ 0`.
The original prime-parameter supplier is
`Localization.Away.SaturatedChart.exists_actual_child_prime_parameter`
(source locator `DoubleLine/Marked.lean:575–608`).
The scheme-point adapter uses that supplier and the existing chart-stalk
comparison. The opposite-chart application swaps the original plane
generators and the same cubic.

Child square classification, a marker and residue bijectivity are supplied
by the later entry and continuation interfaces under their own hypotheses.
The chart-prime construction chooses no coefficient field or completed child.

Present consumers: [CaseTwoChildGenerators](CaseTwoChildGenerators.md), [CaseTwoMarkedStalk](CaseTwoMarkedStalk.md).
