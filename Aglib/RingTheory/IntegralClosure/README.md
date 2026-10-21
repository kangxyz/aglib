# Integral closure

[FlatDescent](FlatDescent.lean), imported as `Aglib.RingTheory.IntegralClosure.FlatDescent`, exports `IsIntegrallyClosed.isIntegrallyClosed_of_faithfullyFlat`. The source and target are commutative domains, the target is a faithfully flat algebra over the source, and the target is integrally closed. The conclusion is integral closedness of the source.

The proof uses the actual fraction-ring map and faithful-flat contraction of principal ideals. Both domain hypotheses remain inputs. This is a public standalone descent result; current smooth-field normality uses its own regular-local stalk route. Original application locators in the source comments remain provenance.

[FractionRing](FractionRing.lean) is a separate generic lower interface. For a Noetherian domain with a specified fraction field and nonzero denominator `b`, `IsFractionRing.isIntegral_div_iff_exists_dvd` characterizes integrality of `a/b` by a nonzero `c` satisfying `b^n ∣ c*a^n` for every natural `n`; `Prime.dvd_of_prime_mul_dvd` and its power version are actual divisibility lemmas. The parameter/normal-quotient helpers retain their stated domain, fraction-field, Noetherian/local and normal-quotient assumptions. `dvd_of_isIntegral_div_of_normal_parameter` assumes a Noetherian local domain, a prime parameter in its maximal ideal, normality of the parameter quotient, and that the parameter does not divide `b`; integrality of `a/b` then gives `b ∣ a`. These helpers require no regular-local hypothesis. [Regular-local normality](../RegularLocalRing/README.md) consumes these lower lemmas after supplying its parameter and quotient hypotheses.

[FiniteEtale](FiniteEtale.lean), imported as `Aglib.RingTheory.IntegralClosure.FiniteEtale`, proves that the literal `integralClosure R A` is finite for a normal Noetherian domain `R`, a specified fraction field `K`, and an etale `K`-algebra `A` with the stated `R`-algebra tower. Over a DVR the same normalization is free and flat. Its localization and tensor generic-fibre equivalence require only integrality over `K`; the equivalence sends `k ⊗ b` to `algebraMap K A k * b`. The coordinatewise finite-product integral-closure equivalence retains the component-finiteness hypotheses and the supplied product decomposition.

[PrimeAway](PrimeAway.md) proves
`IsIntegrallyClosed.of_isLocalizationAway_prime`: for a domain and a prime
element, integral closedness of the actual localization away from that
element implies integral closedness of the original ring. Prime-ideal
lying over gives cancellation for integral fractions, followed by induction
on the actual denominator power. No Noetherian condition is required.
The literal DVR Weierstrass charts use this criterion.
