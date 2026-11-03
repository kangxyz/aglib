# A supplied local surface chain on the same global projective model

Source: [ProjectiveSurfaceChain.lean](ProjectiveSurfaceChain.lean).

`exists_projective_surface_supported_normalizedChain` starts with an
integral normal Noetherian surface `X`, an original finite-coordinate
closed projective embedding over a domain `R`, its original dominant
structural map and finite generic-image base map. At an actual closed
nongeneric point `x`, it consumes the SAME supplied proper normalized-point
chain `p : T → Spec (X.stalk x)` with its genuine dimension bound `dim T ≤ 2`.
For the intended ideal application, the normalized-point domination construction derives
that bound; it is not inferred from an arbitrary birational model.

The existing `SurfaceChain` globalization gives the actual global chain
`f : Z → X`, projection `a : T → Z`, original Cartesian square, equal chain
length and isomorphism off `x`. The chain itself derives integrality,
normality, dominance and invertibility of its original function-field map.
Properness over the original Noetherian scheme derives Noetherianity of `Z`.

Dimension is proved on the original stalks. Points over `x` lift to the
SAME local terminal and the actual localization projection induces stalk
isomorphisms. Away from `x`, the original restriction isomorphism identifies
stalks with those of `X`. Thus both genuine dimension bounds give `dim Z ≤ 2`
without global Nagata, catenarity or a later-stalk finite-over-base premise.

The accepted proper-chain embedding theorem embeds the SAME global `Z` in
`ProjectiveSpace R (ULift (Fin (m + 1)))`, with the exact original structural
triangle. Native original function-field composition proves
`genericImageBaseMap(k) = functionFieldMap(f).comp(genericImageBaseMap(i))`.
The field-map isomorphism and original finiteness then DERIVE finiteness of
the new generic-image map; this is never an extra input.

Only the global terminal is projectively embedded over `R`. The arbitrary
local `T` is retained by the Cartesian square, not declared projective over
`R`. Its original coefficient pulls back through the existing native
`pullbackTriangleIso`. The output permits a later genuine own canonical
object on `Z`; it does not compare that object with the local image line,
prove a canonical epimorphism, a frame, Gorensteinness or resolution.

The support conclusion is the original complement of `x`. It restricts to
every original open avoiding `x` by `Hom.isIso_restrict_of_le`. Consequently
all original regular opens are unchanged when `x` is singular; no such
blanket claim is made for a regular centre.

No regularity, locality, completeness or Noetherianity of `R` is imposed.
The original Noetherian `X`, finite embedding and genuine supplied local
chain are explicit. In the intended canonical context, Noetherianity of
`X` is derived from its original embedding over regular local `R`.

The supported dimension body is now owned once by LocalModification/Dimension
for an arbitrary bound d. This same public theorem calls it at d=2 without
changing its model, hypotheses, maps or outputs.

The original generic-image structural-triangle calculation is now owned
once by ProjectiveSpace/GenericStalk/StructureTriangle. The SAME theorem
calls the lower equality and finiteness laws, retaining all original fields,
maps and hypotheses.
