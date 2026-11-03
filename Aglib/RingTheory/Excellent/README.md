# Excellence and DVR formal fibres

[Defs](Defs.lean), imported as `Aglib.RingTheory.Excellent.Defs`, defines
`IsGRing R` by Noetherianity and regularity of every canonical completion map
from a prime localization of `R` to its maximal-adic completion.
[RegularMap](RegularMap.lean) defines `Algebra.IsRegularMap R S` by flatness
and regularity of the actual tensors `S ⊗[R] E`, for every prime of `R` and
every finite-dimensional extension `E` of its residue field represented in
the source universe. The residue-field scalar tower is explicit. Native
`IsRegularRing` includes Noetherianity; arbitrary infinite field base changes
are not required to be Noetherian.

[GeometricConditions](GeometricConditions.lean) defines the regular locus
using the actual prime localizations. `IsJ2Ring` requires Noetherianity and
openness of this locus in every finite-type algebra. `IsCatenaryRing` requires
Noetherianity and equal lengths for saturated finite prime chains with the same endpoints;
`IsUniversallyCatenaryRing` requires Noetherianity and tests catenarity on
finite-type algebras.
`IsQuasiExcellentRing` combines the G-ring and J-2 conditions, and
`IsExcellentRing` adds universal catenarity.

For `R : Type u`, the J-2 and universal-catenarity tests use algebras in
`Type (max u e)`, with an explicit auxiliary universe `e`. Thus
`IsExcellentRing.{u, e} R` retains this test universe. No invariance under
changing `e` is assumed, and the downstream DVR theorem permits `e` to be
independent of the source-algebra, equation and unknown universes.

[LocalFormalFiber](LocalFormalFiber.lean) uses the maximal-prime component
of a local G-ring domain to prove regularity of its actual finite generic
formal fibres. For a domain DVR, it derives
`AdicCompletion.HasGeometricallyReducedFractionCompletion R`, concerning
the fraction field of the original maximal-adic completion with its canonical
`FractionRing.liftAlgebra` action. [DiscreteValuationRing](DiscreteValuationRing.lean)
supplies this condition from `IsExcellentRing.isGRing`; J-2 and universal
catenarity are not additional inputs to that projection argument.

The current consumer is
[excellent-DVR Artin approximation](../Henselian/DVRArtinApproximation.md)
for actual Henselizations of prime localizations of finite-type algebras.
Its original-ring endpoint additionally assumes `HenselianLocalRing R`.
General stability of excellence, a Nagata theorem and Popescu
desingularization are outside this interface.

[RegularMapStability](RegularMapStability.lean) retains finite base change
and source/target localization for the actual regular-map fibre tests.
[FiniteBranches](FiniteBranches.lean) transfers a regular original
completion map to branches of the whole finite algebra; it does not
assume a selected uncompleted branch finite.
[NormalCompletion](NormalCompletion.lean) proves normal-domain completion
of a normal Noetherian dimension-two local domain from regularity of its
actual completion map.
[FiniteNormalCompletion](FiniteNormalCompletion.lean) applies this to a
normal dimension-two localization of a finite algebra over a G-ring.

[Normalization](Normalization.lean) proves finite integral closure from
the stated regular-completion/G-ring and J-0 or quasi-excellent inputs,
without a dimension bound. The three earlier theorem names ending in
`of_dimLE_two` are retained with the generalized statements.
[J2Criterion](J2Criterion.lean) gives J-2 for semilocal Nagata rings of
dimension at most two. These statements retain their original
rings, localizations and test universes; they do not assert arbitrary
finite-type stability of G-rings or a surface resolution theorem.
