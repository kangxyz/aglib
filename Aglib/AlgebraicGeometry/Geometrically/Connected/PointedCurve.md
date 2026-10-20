# A rational point on a connected smooth proper curve

[PointedCurve](PointedCurve.lean) provides
`Scheme.geometricallyConnected_of_pointed_proper_smooth_curve q o ho`.
Here `q : X ⟶ Spec K` is the original structure map and
`o : Spec K ⟶ X` is its actual rational section, with `ho : o ≫ q = 𝟙 _`.
The hypotheses are `SmoothOfRelativeDimension 1 q`, `IsProper q`,
`IsNoetherian X`, and `ConnectedSpace X`, for a field `K : Type u` and
`X : Scheme.{u}`. The conclusion is `GeometricallyConnected q` for this same
map. No characteristic restriction is imposed.

The proof uses smooth normality and connected Noetherian normal components to
obtain integrality. Properness makes the actual global functions integral over
`K`; evaluation at `o` identifies them with `K`. The proved quasi-compact,
separated global-sections base-change comparison identifies the global
functions after every field extension with its constants. A nontrivial clopen
decomposition would glue a nontrivial idempotent global function, which is
impossible in that field.

[PointedCurveConnectedness](../../../../AglibTest/PointedCurveConnectedness.lean)
checks the current finite étale cover consumer: it derives smoothness,
properness, and Noetherianness for the covering source and applies the result
to its actual Over-field map and rational point. Neither the target's
geometric connectedness nor a curve-properties record is needed in that check.
A second check derives Noetherianness and connectedness from a smooth proper
integral source and applies the result to the original `Over.w` origin equation,
as required by the lifted generic-source consumers.

This producer supplies the smooth proper curve applications of migration proof
task `EG-POINTED-GEOMETRIC-CONNECTEDNESS`. The legacy assertion about arbitrary
connected pointed field schemes is broader and remains conditional; this
module neither imports nor claims that unrestricted family.
