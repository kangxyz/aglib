# Smooth base change

This family studies the existing canonical exchange maps. It does not define
replacement inverse images, direct images, or exchange transformations.

## Closed étale comparison

`Etale.lean` proves that the original `higherBaseChangeMap` is invertible;
`EtaleDerived.lean` proves the original `derivedBaseChangeMap` is invertible.
Both concern the literal pullback of any morphism along an étale morphism. Coefficients are arbitrary abelian sheaves. There is
no properness, quasi-compactness, quasi-separatedness, constructibility, or
torsion hypothesis. The four derived-category universes are independent.

The proof transports preservation of injectives from the existing exact
slice lower-shriek adjunction through the actual étale slice equivalence and
`inverseImageEtaleIso`. On injective singles, degree zero is the original
ordinary exchange mate and positive degrees vanish. The native injective
comparison extends this to arbitrary singles; the original shift coherence
and bounded-below Postnikov comparison give the D+ result.

Lower inputs are `EtaleInverseImageInjectives.lean`, the generic slice
`Injectives.lean`, the original ordinary `Stalk/EtaleDirectImageMate.lean`,
and the read-only original exchange, single/higher, and homological comparison
suppliers. No new extension-by-zero functor is constructed.

`EtaleRelativeDimensionZero.lean` specializes both theorems through the native
characterization of étaleness as smoothness of relative dimension zero.

`Horizontal.lean` proves composition and cancellation for the original ordinary
higher exchange without derived-category choices. Its étale specialization
retains the four independent derived worlds used by the existing Cartesian
comparison supplier.

[Locality](Locality.lean) defines `higherExchangeTest` directly on the intrinsic
ordinary `higherBaseChangeMap`, with no derived-category choices. Its etale
cover assembly retains the four independent models used by the actual
Cartesian comparison on the restricted squares.

## Allowed torsion and its original filtered presentation

`AllowedTorsion.lean` defines `IsBaseInvertibleTorsion S F` using local positive
annihilators invertible in `Γ(S, ⊤)`. It proves equivalence with positive
base-invertible annihilators in the original geometric stalks. The base `S`
is explicit and can differ from the scheme carrying `F`.
`AllowedTorsionOrders.lean` identifies this with finite actual additive element
orders in those stalks whose casts are units in the global sections of `S`.

The generic `Sites/Torsion/Annihilator/Allowed.lean` and `AllowedColimit.lean`
use the existing `annihilator`, `annihilatorι`, divisibility transitions, and
coefficient maps. Positive members of a submonoid of the natural numbers are
ordered by divisibility; multiplication gives filteredness. The original
kernel-inclusion cocone is a colimit for allowed local torsion, and its
canonical map is natural in coefficients. Every stage is uniformly killed by
its own positive allowed index. The specialization to `baseInvertibleOrders S`
retains each literal native kernel inclusion.

This is coefficient infrastructure, not a proof of the positive-relative-
dimension smooth exchange theorem. In particular, the factorial diagram for
arbitrary torsion does not in general stay inside the allowed orders.

## Remaining smooth statement

The general smooth theorem for qcqs direct image still requires genuine local
curve effacement, low-degree curve invariance, and tame-cover extension.
The intended torsion orders are invertible on the entire base, not merely at
the coefficient point. The étale theorem makes no assertion about this missing
positive-relative-dimension argument or about an unbounded derived comparison.
