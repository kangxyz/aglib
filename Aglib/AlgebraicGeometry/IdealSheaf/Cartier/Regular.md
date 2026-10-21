# Height-one actual ideals on regular schemes

[Regular.lean](Regular.lean) proves
`Scheme.Hom.idealModule_isLocallyRankOne_of_regularStalks` for an actual closed
immersion `i : C ⟶ X`. The hypotheses are:

- `X` is locally Noetherian;
- `C` is integral;
- every actual `X.presheaf.stalk x` is regular local;
- every actual `RingHom.ker (i.stalkMap c).hom` has height one.

The conclusion is `IsLocallyRankOne X (Scheme.Hom.idealModule i)`. There is no
dimension bound and no supplied UFD, free-ideal, or Cartier-family hypothesis.
The ideal module and its inclusion are the actual `idealModule i` and
`idealInclusion i`.

At each actual ambient stalk, the existing
`IsRegularLocalRing.isDomain_of_regularLocal` derives domainness and the
actual theorem `IsRegularLocalRing.uniqueFactorizationMonoid_of_regularLocal`
in [RingTheory/RegularLocalRing/Factorial](../../../RingTheory/RegularLocalRing/Factorial.lean)
derives native unique factorization. These are proved lower-ring suppliers,
rather than extra premises in the scheme theorem.

The result then applies
`Scheme.Hom.idealModule_isLocallyRankOne_of_factorialStalks` in
[Invertible/Factorial](../Invertible/Factorial.lean). That theorem derives
singleton bases of the actual height-one stalk-map kernels. The shared
[StalkKernel](../Invertible/StalkKernel.lean) implementation identifies them
with the section kernels localized through the canonical germs, spreads their
bases by finite presentation, uses the unit ideal outside the closed image,
and transports them through the actual spectral and restriction maps.

`Scheme.Hom.Cartier.regularCodimOneIdealInvertible` is an inhabitant of the
existing `RegularCodimOneIdealInvertible` proposition in
[Interfaces](Interfaces.lean). It retains that proposition's original schemes,
universe, locally Noetherian and integral conditions, actual closed immersion,
regular-stalk premise, and height-one stalk-kernel premise. It does not replace
the proposition with a weaker surface specialization. The height-one premise
remains explicit.
