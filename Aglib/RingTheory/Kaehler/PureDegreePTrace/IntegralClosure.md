# Global ordinary differential trace of the literal normalization

Source: [IntegralClosure.lean](IntegralClosure.lean).

Fix a normal Noetherian domain A, its original fraction field K, a finite
purely inseparable extension L/K of prime degree p in characteristic p,
and a coefficient ring Λ with the displayed original scalar towers. Let
B=integralClosure A L be finite over A. For positive degree r=n+1 put

```text
M = exteriorPower A r Ω_(A/Λ),
N = exteriorPower B r Ω_(B/Λ),
L_A = Hom_A(Hom_A(M,A),A).
```

The global construction assumes only that the actual raw M is finite over
A. It does not assume M is reflexive, torsion-free or free, and does not
require N to be finite. `integralClosureTraceTransposeOfNagata` derives
finiteness of B from the original Nagata condition. A,K,L share a universe
in that wrapper because of the Japanese arbitrary-fraction-field API; the
finite-normalization core permits arbitrary universes.

`integralClosureRawTraceAtFraction` is the actual field differential trace
restricted along the original raw exterior map B→L. For each original
height-one q, `integralClosureRawTraceAtFraction_denominator` maps the raw
form into the literal normalization of A_q. Its derived monogenic
presentation supplies an integral local differential trace. The actual
trace scalar-square law identifies its generic value with the original
field value. Surjectivity of the actual target exterior localization map
then gives a denominator s outside q whose multiple comes from M.

`integralClosureRawTraceAtFraction_heightOne` supplies the canonical map
A_q→K and the original scalar towers. The resulting height-one membership
is proved, not assumed. Normal height-one intersection, applied through
the original dual functionals, gives `integralClosureRawTrace : N → L_A`
using the actual bidual embedding `doubleDualToFraction`.

The requested transpose is

```text
c_B(ω)(b) = integralClosureRawTrace(b • ω).
```

Its original generic evaluation, uniqueness, coordinate independence and
pointwise B-action law are proved. No B-action on L_A is introduced.

`doubleDualToFraction_isLocalizedModule` derives localization of the actual
coefficient embedding by localizing the two original duals. Finite M over
Noetherian A supplies the required finite presentations. Together with the
original B→L localization, this defines the actual Hom localization map
`integralClosureTraceHomToFraction`. The theorem
`integralClosureTraceTranspose_localization` proves that native
`IsLocalizedModule.mapExtendScalars` of c_B equals the original field
differential transpose. Two actual localized-module extensionality
arguments reduce its equation to original raw forms and original b∈B.

Generic bijectivity retains the actual generic line dimensions and a
nonzero wedge η∧da over K. No integral unit generator, trace-membership
oracle, supplied trace square or ordinary inseparable field trace is used.
All arguments include characteristic 2 and arbitrary residue fields.

The fixed cokernel annihilator, reflexive-source and sheaf assembly,
canonical proper trace comparison, and the geometric H1 bound are
separate consumers. The scalar maps in this module retain the fixed Λ.

## Geometric use
The construction targets the literal double dual and retains the original
fraction-field and localization formulas. The geometric H1 application
still requires its original trace-functional identification.

Direct consumers: [AlgebraicGeometry/Surfaces/Birational/NormalizedBlowupCover/Trace/RawChart](../../../AlgebraicGeometry/Surfaces/Birational/NormalizedBlowupCover/Trace/RawChart.md), [RingTheory/Kaehler/PureDegreePTrace/Coinduction](Coinduction.md), [RingTheory/Kaehler/PureDegreePTrace/Cokernel](Cokernel.md).
