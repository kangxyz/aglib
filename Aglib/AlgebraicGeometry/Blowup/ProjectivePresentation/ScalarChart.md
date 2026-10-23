# Scalar-extended saturated blowup charts

[ScalarChart.lean](ScalarChart.lean) constructs the actual full tensor chart
ring equivalence, its original coefficient and ratio equations, and both
projections into the literal base-changed blowup. The already proved native
cartesian degree-one chart square supplies the original Proj map equation.
The original Rees irrelevant ideal gives the actual denominator chart cover.

`ChartTriangleEq` retains the literal composition equation and its three
original morphisms. Both the public Proj comparison and its pullback first
projection use this same proposition. Generic pastes consume its `.eq`
field before concrete specialization; all maps and equations are proved.

`gradedChartArrowWithEquation` constructs the whole native chart witness
before the Rees specialization. It takes the original Away algebra
equivalence and constructs the scalar tensor comparison and its original
coefficient square in the same generic body. The public `scalarChartToProj`, its equality
with the original ring-chart map, and its commuting triangle project the
same `scalarChartToProjData`. Thus the witness retains the original arrow
as well as its equation.

All ring and ideal data retain their original scalar structures. No flatness,
domain, reducedness, or blowup-of-image-ideal identity is used.
