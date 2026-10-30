# Actual small-etale first cohomology

`Basic` uses Mathlib's actual `Sheaf.H L 1`, with coefficient maps and structural
Ext universes. Declarations belong to `AlgebraicGeometry.Scheme.EtaleCohomology`.
`HasSheafify` and `HasExt` remain explicit where the chosen universes require
them; the larger-universe suppliers retain their stated ranges.

The torsor leaves construct sheaves, extension classes, coefficient pushouts,
contracted sums and pullbacks on this same cohomology object. The represented
coefficient/torsor leaves compare actual finite-etale group schemes, coefficient
sheaves and their canonical maps. They reuse the single generic continuous-H1
quotient and its affine torsor carrier.

The underlying Set-sheaf language is the actual `Scheme.EtaleTopos X` and its
induced geometric morphism `Scheme.etaleToposMorphism f`, provided below H1 by
`Sites/EtaleTopos`. `TorsorAdjunction` uses its direct image in the carrier-map
data and extension lift; `SchemeTorsorBaseChange` uses it for the represented
section map. The original section values and native units/counits are retained.
Abelian and module coefficient images keep their actual coefficient
adjunctions and universe ranges. `DegreeZeroPullback` obtains the constant/Gamma
transport equation from the shared adjunction Hom-mate proof.

`FundamentalGroupComparison` gives the finite-coefficient comparison with the
specified fibre functor and marking. `MarkedComparisonTransport`, `Naturality`,
`PointedNaturality`, `PointedFieldTransport`, `PointedCoefficientNaturality` and
`CoefficientStalkBaseChange` transport the actual displayed comparison maps.
The existing finite-representation and marked comparison interfaces retain
their positive globally invertible level, annihilator, local trivializations,
markings, actual point and every explicit GC/FF hypothesis required by each
theorem. The separate proper-henselian results below apply to every actual
finite locally constant abelian sheaf and impose no order-invertibility premise.
No supplier is inferred from the presence of an abstract classification
interface.

[FiniteTorsorRepresentation](FiniteTorsorRepresentation.lean) specializes the
[generic slice trivialization](../../../CategoryTheory/Sites/Torsor/ChartTrivialization.lean)
at the original etale test maps. Its chart components are the same
`sectionEquiv` maps; geometric covers and the Stacks03RV representative remain
in this family. [TorsorFunctoriality](TorsorFunctoriality.lean) specializes the
[generic pushout and inverse-image class operations](../../../CategoryTheory/Sites/Torsor/Functoriality.lean),
retaining native Stacks03AJ headers and independent Ext universes.

Generic Kan extension and extension-pushout algebra live below this family in
`CategoryTheory`; finite-etale sheaf descent lives in
`Scheme.FiniteEtale.SheafDescent`. Current consumers are the fundamental-group
comparison endpoints and downstream finite-coefficient applications. Tate
coefficient sheaves, elliptic and arithmetic applications are not admitted here.

[FiniteEtaleRigidity](FiniteEtaleRigidity.lean) detects actual finite-coefficient
H1 classes under fullness of the specified finite-etale pullback functor; that
fullness and the represented-coefficient comparisons remain inputs.
[Kummer/PowerFiber](../Kummer/PowerFiber.lean) constructs the actual fibre torsor
of a supplied power-equivariant multiplicative-torsor map. It retains positive
level and invertibility of that level in the global sections.

## Proper henselian finite coefficients

[ConstantFinite](ConstantFinite/README.md) proves bijectivity of the original
closed-residue pullback on `H1Etale` for every finite constant additive
coefficient group, over any proper scheme above a henselian local ring. The
constant coefficient is compared by the actual `inverseImageConstantIso`;
source and target `HasExt` universes remain separate. The same H1 argument
works for every actual finite locally constant abelian sheaf. The corresponding
sections and original `H0` maps are documented in
[H0/ProperHenselian](../H0/README.md). These finite-coefficient conclusions
do not assert arbitrary-sheaf proper base change.

The [all-coefficient stalk inverse-image comparison](../GeometricPoints/InverseImage/README.md)
proves the original `stalkUnit` isomorphism for every standard-value abelian
sheaf, independently of finite-local-constant or Ext hypotheses. This is a
stalk comparison, not an H1 or proper-base-change theorem.

[FiniteCoefficientClosure](FiniteCoefficientClosure.lean) supplies finite-power
trivializations with the original charts, covering witnesses and finite values.
Its categorical product comparison and value finiteness come from
[the generic product leaf](../../../CategoryTheory/Sites/Pullback/FiniteProducts.lean).
The published cut contains the finite-power interface used by `Fields/FiniteProducts`.

[RepresentedCoefficients](RepresentedCoefficients.lean) obtains its original additive stalk evaluation and inverse from [the general point construction](../../../CategoryTheory/Sites/Point/RepresentedAdditive.lean). The coefficient group, field-valued point, lifted section values and original germs remain unchanged.

[Naturality](Naturality.lean) defines stalk pullback by the inverse of the one original all-coefficient stalk-unit isomorphism and proves agreement with its represented coordinate view. [CoefficientStalkBaseChange](CoefficientStalkBaseChange.lean) and [PointedNaturality](PointedNaturality.lean) retain the actual unit, coefficient, section, point and action equations. The finite/Galois/marking hypotheses of the represented H1 comparison remain at their existing callers; the underlying all-coefficient stalk comparison is separate from H1 classification.
