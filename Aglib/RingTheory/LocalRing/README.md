# Local rings

[ParameterAvoidance](ParameterAvoidance.lean), imported as `Aglib.RingTheory.LocalRing.ParameterAvoidance`, proves the positive-dimensional Noetherian local-ring avoidance step: a first minimal generator can be chosen outside every minimal prime. The separate prime-parameter domain result retains the actual principal-prime and avoidance hypotheses; regularity is not assumed for those lower lemmas.

[ParameterQuotient](ParameterQuotient.lean) lifts a nonzero cotangent vector to a minimal generating family containing the specified parameter. For a Noetherian local ring with cotangent-space dimension at most `d+1` and `x` in the maximal ideal but not its square, `IsLocalRing.spanFinrank_maximalIdeal_quotient_parameter_le` bounds the quotient maximal-ideal generator number by `d`, using the stated local-ring instance on the quotient. No regular-local premise is used. The regular quotient and exact dimension-drop endpoint is separately implemented in [RegularLocalRing/ParameterQuotient](../RegularLocalRing/ParameterQuotient.lean).

Native owners follow the actual local/regular-local mathematical subject. These two parameter leaves feed [regular-local domain/parameters/normality](../RegularLocalRing/README.md). Their source statements preserve the nonzero cotangent, dimension and generator conditions used by the induction.

[SeparatedPrincipal](SeparatedPrincipal.lean), imported as `Aglib.RingTheory.LocalRing.SeparatedPrincipal`, treats a local ring with a specified principal maximal-ideal generator. A finite bound on maximal-ideal order yields a unit-power factorization; Hausdorff separation yields such a bound for each nonzero element. If every generator power is nonzero, the same ring is a domain and then a DVR, without a Noetherian hypothesis. [Adic-completion DVR structures](../AdicCompletion/DiscreteValuationRing.lean) use this criterion.

[ResidueTensor](ResidueTensor.lean), imported as `Aglib.RingTheory.LocalRing.ResidueTensor`, gives closed-base-fibre Nakayama, surjectivity and finite-kernel injectivity tests over a local algebra. The original local structure-map, finite-module and quotient-flatness premises are explicit; no Noetherian assumption is introduced.

[ResidueFieldComap](ResidueFieldComap.lean): for a ring map `σ : A →+* B` and `t ∈ Spec B` over `s = σ⁻¹ t`, `Ideal.ResidueField.mapComap σ t : κ(s) →+* κ(t)` is `Ideal.ResidueField.map` over `σ`; the square `A → B → κ(t)`, `A → κ(s) → κ(t)` commutes (`Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp`), and `κ(s) → κ(t)` is flat (`Ideal.ResidueField.flat_mapComap`). The fibre comparison of cohomology base change (`Cohomology/BaseChange/Modules/Composite`) consumes them.

[PrincipalMaximalIdeal](PrincipalMaximalIdeal.lean) is the lower native
principal-maximal-ideal provider used by the smooth-curve stalk constructions.
The geometric consumers keep their own field, smoothness and dimension inputs.
