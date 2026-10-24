# The actual normalized blowup of a nonzero ideal

Companion to `NormalizedBlowupCover.lean`. The current native stage constructs
only the base normalized blowup and its actual image ideal. Construction of the
second normalization in the original finite separable extension remains open.

## Input and literal construction

In `AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.Base`, let `A` be
a domain and `J : Ideal A` satisfy `hJ : J ≠ ⊥`. No locality or normality of `A`
is needed for these base statements. The unit ideal is allowed.

- `datum A J` is exactly `Blowup.blowupDatum (Blowup.affineCenter A J)`.
- `source A J hJ` and `map A J hJ` are its actual source and blowdown.
- `gamma A J hJ` is the original generic inclusion of this blowup.
- `normalization A J hJ` is exactly `(gamma A J hJ).normalization`.
- `nu A J hJ` is its original normalization map.
- `a A J hJ` is literally `nu A J hJ ≫ map A J hJ`.

The original blowup and normalization are integral. Their original arrows are
dominant. `normalization_normalStalks` proves normality at every actual stalk.
`map_fieldMap_isIso` and `a_fieldMap_isIso` concern the original function-field
homomorphisms; no unrelated field equivalence replaces them.

With `IsNoetherianRing A`, `ringKrullDim A ≤ 2`, and
`IsNagataRing.{u, 0} A`, `nu_isFinite` proves finite normalization, `a_isProper`
proves properness, and `normalization_isLocallyNoetherian` proves local
Noetherianity. The chart argument uses the literal structural scalar map,
its injection and compatibility with germs, a linear algebraic equation in the
original function field, and GF2 on those actual finite-type domain charts.
Neither finiteness of normalization nor a dimension bound on the constructed
source is an added premise.

## Actual ideal and nonflat frames

`ordinaryIdeal` is the image of the original affine centre on the actual
blowup. `imageIdeal` is its inverse image under `nu`;
`imageIdeal_eq` identifies it with the image of that same centre under `a`.
`imageIdeal_isLocallyRankOne` proves invertibility of this actual ideal, and
`imageIdeal_nonzero_localFrame` supplies, near every point, an affine open and
a nonzero regular generator of its literal section kernel ideal.

The enclosing namespace provides `idealPullbackIso` for a dominant morphism
between integral schemes and a Cartier ideal missing the target generic point.
`idealPullbackIso_inclusion` retains its original inclusion into the structure
sheaf. `imageIdeal_isLocallyRankOne` and `imageIdeal_nonzero_localFrame` derive
invertibility and nonzero frames after this possibly nonflat pullback. The
proof uses the actual closed-subscheme pullback square and integral avoidance.
No flatness assumption is introduced.

## Providers and consumer boundary

The same-field chart and normalization arguments generalize the maximal-ideal
construction in `Surfaces/RationalSingularities/Blowup.lean`. Their providers
are `Blowup.Integral`, `Blowup.Properness`, `Blowup.AffineCenter.Support`,
`Normalization.FunctionField`, `IdealSheaf.Cartier.Avoidance`, and
`RingTheory.Nagata.FiniteTypeSurface`.

The second normalization `Y` in the original `L`, its finite map to `X`,
map to `Spec B`, structural square, birationality and ideal frames are
provided by [Finite](NormalizedBlowupCover/Finite.md) and
[Nagata](NormalizedBlowupCover/Nagata.md). The projective row and map to the
original proper model belong to [FiniteDomination](FiniteDomination.md).
