# Actual small-etale first cohomology

`Basic` uses Mathlib's actual `Sheaf.H L 1`, with coefficient maps and structural
Ext universes. Declarations belong to `AlgebraicGeometry.Scheme.EtaleH1`.
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
Finite locally constant coefficients retain their positive globally invertible
level, annihilator, local trivializations, markings, actual point and every
explicit GC/FF hypothesis required by each theorem. No supplier is inferred
from the presence of an abstract classification interface.

Generic Kan extension and extension-pushout algebra live below this family in
`CategoryTheory`; finite-etale sheaf descent lives in
`Scheme.FiniteEtale.SheafDescent`. Current consumers are the fundamental-group
comparison endpoints and downstream finite-coefficient applications. Tate
coefficient sheaves, elliptic and arithmetic applications are not admitted here.

[FiniteEtaleRigidity](FiniteEtaleRigidity.lean) detects actual finite-coefficient
H1 classes under fullness of the specified finite-etale pullback functor; that
fullness and the represented-coefficient comparisons remain inputs.
[Kummer/PowerFiber](Kummer/PowerFiber.lean) constructs the actual fibre torsor
of a supplied power-equivariant multiplicative-torsor map. It retains positive
level and invertibility of that level in the global sections.
