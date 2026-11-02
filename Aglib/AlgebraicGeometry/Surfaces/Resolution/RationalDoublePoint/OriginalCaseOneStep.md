# Original Case-I parameter selection and succession

API: [exists_good_parameter](OriginalCaseOneStep.lean#L60), [exists_fixed_parameter_successor](OriginalCaseOneStep.lean#L103).

This leaf contains two thin adapters on an arbitrary original scheme step
X/x/B/y. Both use the same existing point-localization square and the actual
original point-local-ring map; no other blowup, path or normalized model is
introduced.

`exists_good_parameter` uses the real next closed singular child to select a
good parent generator. Its parent full cone is actual and globally nonsquare.
The selected parent ring and residue field are already the original ones;
there is no generic-hyperplane, rational-point or field-size premise. Parent
normality, rationality and dimension hypotheses are not added to this selector.

`exists_fixed_parameter_successor` additionally uses the genuine normal
Noetherian Nagata rational surface hypotheses. The existing ordinary-local
producer derives the child generators, rank-three Hilbert function, full
kernel and nonreturn. The adapter transports that full output back to the
original child stalk through the original epsilon, not through degreewise
Hilbert ranks. No child Hilbert/kernel/rank, Gorensteinness, canonical frame,
completeness, finite-over-parent or future-marker premise is supplied.

The output retains p=f(t), minimality, centre ideal span{p}, bijectivity of the
actual residue map, a genuine quadratic generating the entire canonical
kernel, nonreturn, nonzero nonsquare first-zero binary restriction and the
native next Case-I presentation. The same scalar parameter remains good.

The existing general cotangent-kernel ring-equivalence law and ParameterEquiv
are reused unchanged. Coefficients use the original ResidueField.mapEquiv.
Existing homogeneous-map and scalar-homogeneous-square-map-iff laws transport
polynomial properties. The only private new polynomial equation is naturality
of the literal eval₂Hom substitution ![0,X0,X1] with coefficient mapping;
it is proved by the native polynomial homomorphism extensionality laws.
There is no second cone, nonsquare, chart or parameter backend.

`OriginalPathCones` uses these successors to construct the later full
cones. `OriginalMixedPath` uses their scalar, centre and residue equations
to fill the existing `Marking` fields on the Case-I tail.

Present consumers: [OriginalPathCones](OriginalPathCones.md).
