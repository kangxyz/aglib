# Original chart maps and Spec squares

[ChartMap.lean](ChartMap.lean) owns `ScalarChartCoordinates.ringChartMap`
and `spec_square_paste`. The first constructs the actual native degree-one
Proj chart from a specified ring equivalence. The second pastes the actual
four ring maps and their proved equations. Both are used by the scalar Rees
chart and graded augmentation consumers; no projectivity premise is present.
