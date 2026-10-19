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

[Reduced](Reduced.lean), imported as `Aglib.RingTheory.Smooth.Reduced`, gives `Algebra.Etale.etale_isReduced`, the standard-smooth reducedness result and the smooth-algebra reducedness result in their native owners. The base is an arbitrary commutative domain; the algebra is commutative with the stated etale/standard-smooth/smooth structure.

The etale result uses actual flat injection into the generic fibre, whose unramified field algebra is reduced. Polynomial presentation/localization gives the smooth result. No field or characteristic assumption is placed on the base domain. [Smooth scheme reducedness](../../AlgebraicGeometry/Morphisms/Smooth/Reduced.lean) is the concrete consumer.

[AdicCompletion](AdicCompletion.lean), imported as `Aglib.RingTheory.Smooth.AdicCompletion`, lifts quotient-valued maps from a formally smooth algebra to a finite target algebra over a Noetherian ideal-adically complete base. It also proves surjectivity of the actual quotient tensor-base-change map on algebra homomorphisms. The [finite-module completeness input](../AdicCompletion/FiniteModule.lean) uses the given ideal and extended ideal; neither result requires a local-ring hypothesis.
