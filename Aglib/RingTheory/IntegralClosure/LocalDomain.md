# Domainhood of reduced integrally closed local rings

`IsIntegrallyClosed.isDomain_of_artinian_total_fraction_ring` retains the
original theorem and proof extracted from `AdicCompletion/NormalSurface`:
a local integrally closed ring whose supplied genuine total quotient ring
is reduced and Artinian is a domain. The Artinian decomposition provides
idempotents, integral closedness lifts them, and locality forces a single
field factor. The supplied coefficient map and same-universe interface are
unchanged. The two idempotent helpers have one implementation here.

`IsIntegrallyClosed.isDomain_of_isLocalRing_of_isReduced` applies this to
a reduced Noetherian integrally closed local ring, proving Artinianity of
its native `FractionRing` with `Localization/TotalFractionRing`. Domainhood
is a conclusion, not part of the integral-closedness hypothesis. No
zero-dimensionality of an unrelated generic formal fibre is used.
