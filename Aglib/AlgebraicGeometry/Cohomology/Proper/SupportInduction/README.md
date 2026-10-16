# The actual closed-support induction step

[SupportInduction](../SupportInduction.lean) is an explicit induction step.
Its smaller-support premise quantifies actual closed immersions `i : Z ⟶ X`
whose topological ranges lie in a specified closed set, coherent coefficients
on those actual sources, and their original integer single placements. It
does not assume the desired conclusion for arbitrary proper morphisms.

On a Noetherian source, `coherent_derivedSingle_of_closed_support` descends
each supported coherent module directly to a positive power of the native
`vanishingIdeal`. The coefficient on the actual thickening is its ordinary
pullback. The conclusion transfers through the original
`closedImmersionDerivedDescentIso`, whose first factor is the original
ordinary adjunction unit and whose remaining factors are the native
exact-single and installed derived-composition comparisons. There is no
global-annihilator construction, prime filtration or alternative cohomology.

`coherent_derived_of_closed_support` applies the sole shared finite Postnikov
theorem to the actual bounded coherent object's original homology layers.
The target property is coherence of every native homology sheaf of the
installed `RF`; it does not impose an output upper bound.

`coherent_derivedSingle_of_modification` combines this step with the actual
[ordinary modification triangle](../Modification/README.md). Its third
object has bounds `[-1,N]` and boundary support, and its image is controlled
by the smaller-support premise. The actual image of the middle object is
the composite direct image through the original
`derivedPushforwardPlusCompIso`. Native triangle closure then proves the
conclusion for the original coefficient's derived image. The two
modification-image coherence inputs and actual upper bound remain explicit
in this lower step. The proved coefficient-independent Chow producer
supplies them in the unconditional proper theorem, whose Noetherian
induction must instantiate the smaller-support premise internally.

The exact source passed with receipt `1792122070504429000-42966` in
4.5 seconds at the default budget. The independent arbitrary-universe
`ProperSupportInductionConsumer.lean` passed with receipt
`1792122124080312000-43399`; all three inspected declarations use only
the three standard axioms. The exported modification step explicitly
retains the smaller-boundary premise and the actual native coefficient,
modification images and derived interval.
