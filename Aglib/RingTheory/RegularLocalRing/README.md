# Regular-local rings

[Domain](Domain.lean) exports `IsRegularLocalRing.isDomain_of_regularLocal`; [Normal](Normal.lean) exports `IsRegularLocalRing.isIntegrallyClosed_of_regularLocal`. Both assume a commutative regular local ring. Domain and integral closedness are conclusions, not extra premises. [DimensionZero](DimensionZero.lean) shows the dimension-zero ring is a field.

[ParameterQuotient](ParameterQuotient.lean) gives `IsRegularLocalRing.regularLocal_quotient_parameter`, retaining the actual first-generator/cotangent conditions and proving the regular quotient with exact dimension drop. [Parameters](Parameters.lean) gives `IsRegularLocalRing.exists_regular_parameter`: positive dimension yields a scalar-regular first parameter whose quotient is regular local and has dimension one less. The finite-dimensional induction uses the actual maximal ideal and Krull-dimension equality. Lower [parameter avoidance/quotient](../LocalRing/README.md) and generic fraction calculations supply the intermediate ring arguments.

[Etale](Etale.lean) extends `Algebra.FormallyUnramified` with `ringKrullDim_eq_of_flat` and `isRegularLocalRing_of_flat`. The source/target are Noetherian local rings, the algebra map is local and essentially finite type, flatness and formal unramifiedness are supplied, and source regularity is needed for target regularity.

Focused imports are `Aglib.RingTheory.RegularLocalRing.Domain`, `.Normal`, `.Parameters` and `.Etale`. [Smooth scheme regularity/normality](../../AlgebraicGeometry/Morphisms/Smooth/README.md) uses the actual ring theorems at scheme stalks. The general domain and normality endpoints impose no dimension-one hypothesis; the following leaf separately handles dimension-one and Artinian quotients.

[ArtinianQuotient](ArtinianQuotient.lean), imported as `Aglib.RingTheory.RegularLocalRing.ArtinianQuotient`, supplies the existing dimension-one DVR, actual Artinian kernel-basis and regular principal-kernel results. The localized-basis supplier retains global Noetherianity; the principal-kernel regularity result retains only its stated maximal-local-ring conditions.

[Localization](Localization.lean) supplies the localized regular-local-ring
interfaces used by the operator and stalk families; their displayed regularity
and localization hypotheses remain explicit.

[Residue projective dimension](ResidueProjectiveDimension.md) proves regularity
of a commutative Noetherian local ring from finite actual projective dimension
of its residue field, using the minimal-resolution/Koszul cotangent lower bound.
[Flat descent](FlatDescent.md) then proves regularity of the source of an actual
flat local homomorphism from a Noetherian local ring to a regular local ring.
The ring universes are independent; no finite-type, unramifiedness,
characteristic or completion premise is imposed.

[HeightOnePrincipal](HeightOnePrincipal.md) proves that every height-one prime
of a regular local ring with `ringKrullDim R ≤ 2` is principal, with a singleton
basis on the actual ideal. In dimension exactly two, every nonmaximal prime
is principal, including the zero ideal; its nonzero case has the same basis.
The [regular-surface ideal consumer](../../AlgebraicGeometry/IdealSheaf/Invertible/RegularSurface.md)
uses these actual ideal bases to prove local rank one of `idealModule i` for
a closed immersion `i : C ⟶ X`. It retains integral `C`, locally Noetherian
`X`, regular ambient stalks of dimension at most two, and height one of every
actual kernel `RingHom.ker (i.stalkMap c).hom`. This leaf retains its
dimension-at-most-two interface.

[PrimeLocalization](PrimeLocalization.md) proves regularity of every actual
prime localization from regularity of the original local ring, and derives
native `IsRegularRing R`. Its arbitrary prime-localization-model version
allows independent source and target universes.
[PrincipalLocalization](PrincipalLocalization.md) proves principality of an
actual extended ideal when that same localized ideal is projective, using
finite projective dimension of the original finite ideal.

[Factorial](Factorial.md) proves native `UniqueFactorizationMonoid R` for every
commutative regular local ring, with no dimension bound. It also supplies
`isPrincipal_of_height_eq_one` and `heightOneIdealBasis` on each actual
height-one prime. Dimension induction combines the original finite ideal's
stable free complement with rank-one cancellation and native prime-element
localization descent. The [regular-stalk Cartier consumer](../../AlgebraicGeometry/IdealSheaf/Cartier/Regular.md)
uses these actual ideal bases in every dimension, retaining local
Noetherianity, integrality of the closed subscheme, and height one of the
actual stalk-map kernels.

[QuotientLift](QuotientLift.md) lifts regular locality from the quotient of a
Noetherian local ring by an actual nonzerodivisor. Minimal quotient generators
lift together with the original equation; no additional condition outside the
square of the maximal ideal is needed. Its localization form uses the same
mapped ideal and quotient. The actual regular-point blowup stalk proof uses
this lower result.
