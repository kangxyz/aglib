# Literal quotient source in principal refinement

`LiteralQuotient.lean` proves the original quotientMap square Cartesian when
the supplied target ideal is genuinely equal to the mapped source ideal.
This is structural ideal data, not a desired comparison-map equality.
The quotientMap, its scalar action and its literal target quotient remain
unchanged. Openness follows from that same Cartesian square; the existing
scalarExtensionPushoutIso supplies its original unit equation.

For R→S, t:R, R_t=Away t, S_t=Away(alpha(t)), the original Away.map satisfies
the ring square. Ideal.map_map proves

    (I.map alpha).map(locS) = (I.map locR).map(alpha_t).

Thus the actual target restriction delta_S is the original quotientMap
into the literal refined target ideal on the right. Its Cartesian and open
properties are proved, not passed as extra hypotheses. No source ring
isomorphism or replacement quotient presentation is constructed.

The principal target specialization explicitly supplies the original source ring S and the bundled localization of its actual carrier to the literal quotient laws. This fixes elaboration of the existing quotientMap condition and open-immersion instance without changing either scalar action.
