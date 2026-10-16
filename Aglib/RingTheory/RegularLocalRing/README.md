# Regular-local domain, parameters and normality

[Domain](Domain.lean) exports `IsRegularLocalRing.isDomain_of_regularLocal`; [Normal](Normal.lean) exports `IsRegularLocalRing.isIntegrallyClosed_of_regularLocal`. Both assume a commutative regular local ring. Domain and integral closedness are conclusions, not extra premises. [DimensionZero](DimensionZero.lean) shows the dimension-zero ring is a field.

[ParameterQuotient](ParameterQuotient.lean) gives `IsRegularLocalRing.regularLocal_quotient_parameter`, retaining the actual first-generator/cotangent conditions and proving the regular quotient with exact dimension drop. [Parameters](Parameters.lean) gives `IsRegularLocalRing.exists_regular_parameter`: positive dimension yields a scalar-regular first parameter whose quotient is regular local and has dimension one less. The finite-dimensional induction uses the actual maximal ideal and Krull-dimension equality. Lower [parameter avoidance/quotient](../LocalRing/README.md) and generic fraction calculations supply the intermediate ring arguments.

[Etale](Etale.lean) extends `Algebra.FormallyUnramified` with `ringKrullDim_eq_of_flat` and `isRegularLocalRing_of_flat`. The source/target are Noetherian local rings, the algebra map is local and essentially finite type, flatness and formal unramifiedness are supplied, and source regularity is needed for target regularity.

Focused imports are `Aglib.RingTheory.RegularLocalRing.Domain`, `.Normal`, `.Parameters` and `.Etale`. [Smooth scheme regularity/normality](../../AlgebraicGeometry/Morphisms/Smooth/README.md) uses the actual ring theorems at scheme stalks. No dimension-one or DVR application is part of this family.

[ArtinianQuotient](ArtinianQuotient.lean), imported as `Aglib.RingTheory.RegularLocalRing.ArtinianQuotient`, supplies the existing dimension-one DVR, actual Artinian kernel-basis and regular principal-kernel results. The localized-basis supplier retains global Noetherianity; the principal-kernel regularity result retains only its stated maximal-local-ring conditions.
