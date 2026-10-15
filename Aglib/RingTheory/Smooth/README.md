# Reduced smooth algebras over domains

[Reduced](Reduced.lean), imported as `Aglib.RingTheory.Smooth.Reduced`, gives `Algebra.Etale.etale_isReduced`, the standard-smooth reducedness result and the smooth-algebra reducedness result in their native owners. The base is an arbitrary commutative domain; the algebra is commutative with the stated etale/standard-smooth/smooth structure.

The etale result uses actual flat injection into the generic fibre, whose unramified field algebra is reduced. Polynomial presentation/localization gives the smooth result. No field or characteristic assumption is placed on the base domain. [Smooth scheme reducedness](../../AlgebraicGeometry/Morphisms/Smooth/Reduced.lean) is the concrete consumer.
