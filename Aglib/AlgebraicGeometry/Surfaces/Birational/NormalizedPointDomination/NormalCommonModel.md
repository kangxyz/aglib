# A constructed normal common model

Source: [NormalCommonModel.lean](NormalCommonModel.lean).

`exists_normalCommonModel` starts with integral `P,S,X,Y`, Noetherian `P`,
normal `S`, and proper dominant birational maps `b : S ⟶ P`,
`f : X ⟶ S`, `g : Y ⟶ S`.
The base `P` has dimension at most two and Nagata nonempty affine charts.

It constructs integral normal Noetherian `Z` of dimension at most two and
proper dominant arrows `a : Z ⟶ X`, `c : Z ⟶ Y` with invertible original
function-field maps. It retains `a ≫ f = c ≫ g` and proves the actual pair
`Z ⟶ X ×[S] Y` finite.

`CommonOpen` constructs the common dense open. `CommonModel` normalizes its
schematic graph component, and `CommonModelOverBase` derives finiteness from
the accumulated map to `P`. The full fibre product is not normalized.

`SelectedElimination` uses this common model at each normalized point step,
derives its proper-image curve embedding, and eliminates a selected curve
by finite DVR-order induction. `CardinalityInduction` then constructs the
dominating chain by strict finite-count induction. This helper supplies
the common model; the consumers supply the two finite inductions.

Present consumers: [SelectedElimination](SelectedElimination.md).
