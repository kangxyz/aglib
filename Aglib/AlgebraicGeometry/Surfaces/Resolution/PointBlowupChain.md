# Exact composition of point-blowup chains

[PointBlowupChain.lean](PointBlowupChain.lean) adds actual proofs to the
existing native chain type in frozen Principalization. Its definition and
previous suppliers are retained in their original owner.

The composition constructor concatenates the original closed-point
blowups over the literal composite g≫f. Source integrality and dominance
continue to come from the existing chain methods.

For an integral original X, functionFieldMap_isIso derives source
integrality, dominance and an isomorphism of the original generic-point
stalk homomorphism. A two-dimensional centre differs from the generic
point because the original generic stalk is a field. The existing
single-blowup field isomorphism and native composition of function-field
maps give the result by induction. There is no added regularity,
Noetherianity, properness or global dimension assumption.

functionFieldEquiv is the resulting canonical ring equivalence and its
forward ring homomorphism is literally Scheme.functionFieldMap f. It does
not select an unrelated field model. Canonical composition of the original
homomorphisms is the existing FunctionField.AffineCharts theorem.

The immediate consumers are original generic-map transport during finite
projective-factor extension and regular-source common domination. Native
compilation and independent mathematical adoption are recorded separately;
this companion does not assert singular resolution or trait comparison.
