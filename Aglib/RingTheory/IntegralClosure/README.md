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

## Finiteness and localization

[NormalHull](NormalHull.md) derives finite literal normalization in every
finite extension of a supplied fraction field from the purely inseparable
cases. The original base is a Noetherian domain. The test fields have the
same universe as the target extension; the base and fraction-field universes
may differ. The actual normal hull, fixed field and ambient inclusions are
retained. No local, normal, complete or dimension premise is added.

[FiniteLocalization](FiniteLocalization.md) proves finite normalization of a
Noetherian domain in its supplied fraction field from two precise inputs:
an actual nonzero normal principal open, and finite literal normalizations
at all maximal localizations. Its denominator filtration uses the same
original element throughout. The local coefficient actions are those of
`atPrimeFractionMap`; local finiteness alone is not the statement of this
criterion.

[FlatBaseChange](FlatBaseChange.md) supplies the actual fraction-tensor
inclusion and faithful-flat finiteness descent used by
[AdicCompletion.Normalization](../AdicCompletion/Normalization.md). That
application proves finite literal normalization in the supplied total quotient
ring for a Noetherian local ring of dimension at most two whose actual
maximal-adic completion is reduced. These maps and hypotheses remain explicit.

[RationalAdjunction](RationalAdjunction.md) supplies the original
polynomial evaluation kernel, numerator-ideal quotient, coefficient-DVR
localization comparison and finite polynomial-value inclusion for adjoining
an actual fraction to a normal domain. The
[Nagata consumer](../Nagata/RationalAdjunction.md) adds the Nagata and
dimension-at-most-two hypotheses to prove finite normalization. Its finite
intermediate and second localization preserve the original ambient field;
the selected final local ring is not assumed finite over the coefficient
localization.

[MaximalIdealDual](MaximalIdealDual.md) identifies the original scalar map
`A → Hom_A(m_A,A)` with a linear equivalence for a normal Noetherian local
domain of dimension at least two. It sends `a` to multiplication by `a`
on the actual maximal ideal. The
[closed-fibre extension calculation](../../AlgebraicGeometry/Cohomology/Proper/ClosedFibreExtensions.md)
uses that scalar to correct a supplied lift; producing the lift is a
separate geometric input.

[TraceLattice](TraceLattice.md) constructs a fixed integral field basis and
its principal-localization basis from an original finite algebra of domains
with compatible fraction fields. Normality gives base-valued traces;
separability gives the nonzero discriminant and injective trace coordinates.
The adjugate identities retain that basis and scalar. The finite-diagram
cohomology consumer supplies the geometric maps and length comparison.
