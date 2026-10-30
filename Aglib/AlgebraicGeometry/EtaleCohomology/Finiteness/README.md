# Geometric finiteness suppliers

These modules retain the original small-etale cohomology, coefficient actions,
and maps. Finiteness and vanishing are separate conclusions. Finite generation
over an arbitrary coefficient ring never means that the underlying additive
group is finite.

## Accepted characteristic-primary and module suppliers

- `ArtinSchreier` proves finite original prime-field and cyclic prime-power
  cohomology for proper schemes over a separably closed field of that
  characteristic, in every degree. There is no dimension-one, smoothness,
  reducedness or perfectness assumption.
- `ConstantModules`, `ConstantPrimaryModules`, and `ConstantModuleSheaves`
  retain the original independent-universe scalar action. Prime-killed finite
  constant modules need no Noetherian ring assumption; the prime-power
  extension argument uses Noetherianity.
- `AbelBoundary` identifies the original graph-divisor Kummer boundary at the
  specified origin. This is not a full Picard divisibility theorem.

## Actual family values and Kummer normalization

- `ProperCurveH1Family/RationalValues` proves finite image from rational local
  constancy on a compact locally finite-type scheme over an algebraically
  closed field. Jacobson closed-complement coverage precedes compactness.
- `ProperCurveH1Family/FibreValues` constructs the original constant-family
  fibre arrow from the specified-square split-base lift, retaining both
  projections and its identity composite to the fixed scheme. Its
  class-difference calculus uses the original H¹ pullback and section
  coefficient isomorphism.
- `KummerFamilyValues` identifies original fixed-coefficient section pullback
  with original roots cohomology pullback through the
  [native roots section producer](../Kummer/SectionPullback.lean) and the
  [original roots composition laws](../Kummer/RootsComposition.lean). Only the
  receiving scheme needs the displayed geometric Galois-category point; the
  family need not be connected.

## Actual curve H1 consumers

`ProperCurveH1Family/EtaleNeighborhood` and `ProperCurveH1Family` are accepted.
They consume actual proper-henselian H1 rigidity and actual chart-limit continuity
to prove finite original family image for a proper fixed scheme and a compact
locally finite-type parameter scheme over an algebraically closed field.
No curve restriction or PBC premise is required.

`KummerChartFiniteValues`, `KummerCurveTorsion`, `KummerCurveH1`,
and `PrimeToCharacteristicCurveH1` assemble that result with the actual bounded
Kummer families. Their endpoints are finite original Picard n-torsion
and finite original roots/cyclic H1 for smooth proper geometrically connected
curves over algebraically closed fields, with n positive and invertible. They are now native accepted.

`PGroupModuleSheaves` is accepted. It consumes the actual
constant subobject/cokernel construction and p-group representation induction,
not arbitrary representation-object descent. The proper finite-cohomology
extension uses a Noetherian coefficient ring and an actual p-group Galois
trivialization with a finite p-killed literal module.

## Boundaries

These cuts do not assert full proper finiteness for arbitrary constructible
modules, compact-support finiteness, constructible exceptional direct images,
general proper base change, H2 Picard divisibility, or full smooth base change.
Those require their remaining geometric and functorial producers. In
particular, no characteristic-primary ordinary nonproper direct-image
constructibility is inferred.

`GaloisModuleSheaves` now removes the p-group restriction through the actual
Sylow intermediate quotient and original coprime trace. It retains the supplied
actual finite-Galois trivialization, finite p-killed literal module, proper
characteristic-p geometry, and Noetherian coefficient ring. No assertion that
every finite-type locally constant module has such a global trivialization
is made. The generic/dense-open and localization consumers remain separate.

`SeparablyClosedCurveH1` extends the roots/cyclic H1 finiteness result to
separably closed, possibly imperfect fields through the literal purely
inseparable finite-cover pullback and original H1 injection. Its original Ext
universe is arbitrary. `PrimeToCharacteristicCurveModules` and
`PrimeToCharacteristicCurveModuleSheaves` then prove finite original H1 for
finite R-modules killed by an invertible prime. The coefficient ring is
arbitrary commutative, with independent universe and no Noetherianity or finite
underlying-group premise. Native large-Ab colimit guards remain explicit.
No H2 or arbitrary constructible-coefficient conclusion is inferred.

`ConstantTorsionCurveH1` and `ConstantTorsionCurveModuleSheaves` extend this
H1 result to every positive annihilator and every finite constant torsion
module over a Noetherian commutative coefficient ring. Their arbitrary-prime
intermediate uses no Noetherianity. `DimensionZeroModules` combines actual
constructible H0 finiteness with positive vanishing to give all-degree original
module finiteness in proper dimension zero over separably closed fields,
without Noetherianity, torsion or reducedness assumptions.
