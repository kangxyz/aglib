# The expanded coefficient entrance on the original ring and field

Source: [Coordinates.lean](Coordinates.lean).

`exists_finite_basis_of_coordinates` takes an actual coordinate equivalence
`e : k[[X,Y]] ≃+* R`, an original fraction field K of R, and an original a
with no pth root in K. It does not replace R or K. The accepted
`RegularLocalRing/FormalCoordinatesTwo` supplies e in the complete regular
characteristic-p dimension-two application.

A root of `e.symm a` in the series ring would map to a root in original K.
The existing `exists_singleSeries_finite_basis` is invoked exactly once to
choose E, positive rank r, and one integral series differential basis b.
Write Lambda = E[[X,Y]]. Its action on R is precisely
`e.toRingHom.comp (scalarMap p hp)`, where scalarMap is coefficient inclusion
followed by p-expansion of both variables. Lambda is not the constant field k.
The Lambda action on original K is this same map followed by original R to K.

The result contains actual `Module.Finite Lambda R` and the explicit transported
basis bR, integral `D Lambda R a ≠ 0`, the original-K differential rank, and
nonzero `D Lambda K (algebraMap R K a)`. The generic outputs are derived from
that same bR by existing fraction-basis APIs, without introducing FractionRing
of a replacement series ring.

The basis is `(b.baseChange R).map tensorKaehlerEquivOfFormallyEtale` for the
actual isomorphism e. Its coordinate proof sends the original coordinates of
d(e.symm a) through e, ensuring integral nonvanishing before localization.
Finiteness is transported by the same Lambda-algebra equivalence. Therefore
`Module.Finite.finiteType` and the native affine `HasRingHomProperty.Spec_iff`
give the actual finite-type Spec(R) to Spec(Lambda) map needed downstream.
This is not inferred from finiteness of differentials alone.

Positive r can be written n+1 without changing bR, meeting the native
`Cokernel.of_basis` basis cardinality. Its integral nonzero-da premise is an
explicit output. Original K to L, its degree, and its actual integral-generator
field presentation remain unchanged in that consumer.

Perfectness, finite absolute p-rank and an externally supplied differential
basis are not inputs.

Direct consumers: [RingTheory/Kaehler/PureDegreePTrace/CompleteRegularEntrance](../../Kaehler/PureDegreePTrace/CompleteRegularEntrance.md).
