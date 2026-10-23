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
