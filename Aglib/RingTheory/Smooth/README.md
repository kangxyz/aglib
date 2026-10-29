# Smooth algebras

[GeometricRegularity](GeometricRegularity.lean) proves
`Algebra.Smooth.of_geometricallyRegular`: a finite-type algebra over an arbitrary
field is smooth when every field base change is a regular ring. Over a perfect
field, `Algebra.Smooth.of_isRegularRing_of_perfectField` only requires the algebra
itself to be regular. The proof uses the local Jacobian criterion and faithfully
flat descent from an algebraic closure.

The lower [regular-local kernel lemma](GeometricRegularity/RegularLocalKernel.lean)
proves `I ⊓ m^2 = m * I` for a regular local ring with regular local quotient.
[LocalCriterion](GeometricRegularity/LocalCriterion.lean) transfers this identity
to the actual cotangent map. The scheme consumer is the
[geometric regularity criterion](../../AlgebraicGeometry/Morphisms/Smooth/GeometricRegularity.lean).

[ArtinianLifting](ArtinianLifting.lean), imported as `Aglib.RingTheory.Smooth.ArtinianLifting`,
proves the Artinian-test criterion `Algebra.FormallySmooth.of_lift_artinianLocal_squareZero`. Let
`R` be any commutative ring and `S` a local `R`-algebra with a surjection `P → S` of `R`-algebras,
where `P` is a Noetherian local `R`-algebra, formally smooth with finite free `Ω[P⁄R]`. Suppose
that, for every surjection `g : A' → A` of `R`-algebras with `A'` Artinian local in the universe
of `P` and `(ker g) ^ 2 = 0`, every surjective `R`-algebra map `S → A` lifts through `g`. Then `S`
is formally smooth over `R`. The proof uses the single extension `P ⧸ 𝔪 J → P ⧸ J`, with
`J = ker (P → S) + 𝔪 ^ m` for the exponent of
[ArtinReesInfMulSup](../Ideal/ArtinReesInfMulSup.lean), and Mathlib's Jacobian criterion
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`. Unlike
[LocalCriterion](GeometricRegularity/LocalCriterion.lean), it imposes no condition on the residue
field. `Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization` applies the
criterion to the localization at a prime of a finite type algebra over a Noetherian `R`, with test
rings in the universe of `R`. It uses the localized polynomial presentation of Mathlib's
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`. The scheme consumer is
[InfinitesimalLifting](../../AlgebraicGeometry/Morphisms/Smooth/InfinitesimalLifting.lean)
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Prop. 5.19, p. 47, applies the
infinitesimal criterion to Artin local test rings).

[Reduced](Reduced.lean), imported as `Aglib.RingTheory.Smooth.Reduced`, gives `Algebra.Etale.etale_isReduced`, the standard-smooth reducedness result and the smooth-algebra reducedness result in their native owners. The base is an arbitrary commutative domain; the algebra is commutative with the stated etale/standard-smooth/smooth structure.

The etale result uses actual flat injection into the generic fibre, whose unramified field algebra is reduced. Polynomial presentation/localization gives the smooth result. No field or characteristic assumption is placed on the base domain. [Smooth scheme reducedness](../../AlgebraicGeometry/Morphisms/Smooth/Reduced.lean) is the concrete consumer.

[AdicCompletion](AdicCompletion.lean), imported as `Aglib.RingTheory.Smooth.AdicCompletion`, lifts quotient-valued maps from a formally smooth algebra to a finite target algebra over a Noetherian ideal-adically complete base. It also proves surjectivity of the actual quotient tensor-base-change map on algebra homomorphisms. The [finite-module completeness input](../AdicCompletion/FiniteModule.lean) uses the given ideal and extended ideal; neither result requires a local-ring hypothesis.

GenericConnectedness owns `Algebra.Smooth.generic_primeSpectrum_preconnected`
and `generic_primeSpectrum_connected`. A connected smooth algebra over an
integrally closed domain stays connected after extension to the supplied
fraction field. The proof lifts generic integral elements and idempotents
and uses the actual idempotent/clopen correspondence. The normal-domain,
smoothness, fraction-field and connectedness conditions remain explicit on
the main results; lower helpers use their stated weaker hypotheses. The
consumer is finite-etale GenericRestriction.

[LocalEquivalence](LocalEquivalence.lean) transports `Algebra.IsSmoothAt`
through a coefficient-compatible algebra equivalence to the actual inverse
image prime, across independent ring universes.
[QuotientImage](QuotientImage.lean) applies this to a surjective generator
evaluation followed by an injective point: smoothness of the original source
at the target-prime inverse image gives smoothness of the literal kernel
quotient at its corresponding prime. The point-factorization equation remains
an input. The polynomial-origin DVR approximation reduction uses this
comparison to retain its original evaluated equation ideal.
