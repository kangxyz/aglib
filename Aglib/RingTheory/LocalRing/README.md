# Parameters and quotient dimension

[ParameterAvoidance](ParameterAvoidance.lean), imported as `Aglib.RingTheory.LocalRing.ParameterAvoidance`, proves the positive-dimensional Noetherian local-ring avoidance step: a first minimal generator can be chosen outside every minimal prime. The separate prime-parameter domain result retains the actual principal-prime and avoidance hypotheses; regularity is not assumed for those lower lemmas.

[ParameterQuotient](ParameterQuotient.lean) lifts a nonzero cotangent vector to a minimal generating family containing the specified parameter. For a Noetherian local ring with cotangent-space dimension at most `d+1` and `x` in the maximal ideal but not its square, `IsLocalRing.spanFinrank_maximalIdeal_quotient_parameter_le` bounds the quotient maximal-ideal generator number by `d`, using the stated local-ring instance on the quotient. No regular-local premise is used. The regular quotient and exact dimension-drop endpoint is separately implemented in [RegularLocalRing/ParameterQuotient](../RegularLocalRing/ParameterQuotient.lean).

Native owners follow the actual local/regular-local mathematical subject. These two leaves feed [regular-local domain/parameters/normality](../RegularLocalRing/README.md). Their source statements preserve the nonzero cotangent, dimension and generator conditions used by the induction.
