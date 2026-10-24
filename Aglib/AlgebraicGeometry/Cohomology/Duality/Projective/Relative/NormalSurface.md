# Chosen-embedding normal-surface concentration

`NormalSurface.lean` uses the original closed immersion into polynomial
projective space and the original derived closed right adjoint. The ambient
coefficient is `relativeTopDifferentialCoefficientsFunctor` at the structure
module, identified with the original top exterior differential sheaf by
`relativeTopDifferentialCoefficientsUnitIso`.

`normalSurfaceTopDifferentialObject` names exactly `Ri!(Ω^n[0])` with the raw
original top exterior coefficient. `normalSurfaceDualizingObjectUnitIso`
is the explicit original coefficient-unit comparison with the
coefficient-functor presentation. Coherence, full support, concentration and
the native single reconstruction are supplied for this raw original object
as well. `normalSurfaceTopDifferentialCanonicalIso_homology` normalizes the
reconstruction by its own original `H^n`.

The conditions are a regular local domain as base, an actual closed immersion
of an integral source with normal stalks and actual topological dimension at
most two, and dominance with finiteness of the original composite
function-field map. The theorem allows arbitrary inseparability. The specified
regular local base of dimension two is included; the proof does not require a
separate base-dimension calculation. Noetherianity of the ambient and the
closed source follows from the genuine regular local base and the finite
projective coordinate type.

The concrete polynomial coefficient frame uses the original Euler frame,
the displayed complement order, native exterior restriction, and the native
top free exterior isomorphism. The coefficient is not globally replaced by a
chosen frame. `normalSurfaceHomology_finitePresentation` obtains coherent
homology from the general original derived finite-source theorem before
support is used.

`normalSurface_localVanishing` constructs an actual affine quotient chart
over each selected original polynomial open. Its stalk isomorphisms are the
original open stalk maps. The local normal-quotient theorem applies to the
actual quotient map in arbitrary finite ambient dimension. The source
dimension bound is obtained from the actual scheme dimension. Its rings and
scalar action are the stalk provider's literal `imagePoint`, `ambientRing`,
`sourceRing`, and `stalkMap` for that quotient chart.

At the generic point, `genericImage_stalk_dimension` uses the same original
function-field map. The original quotient onto the generic source stalk is
a quotient onto a field. A regular parameter list and the original
`topExtRingQuotientLinearEquiv` prove nonvanishing, including the empty list.
Transport through the derived-model and original germ comparisons gives a
nonzero generic homology stalk. Coherence makes its support closed, hence
equal to the whole integral source.

The nonzero degree-n stalk forces the local equality
`dim ambient_stalk = n + dim source_stalk`; the same Ext vanishing then kills
every other nonnegative degree. Negative degrees vanish from the original
injective resolution. `normalSurfaceCanonicalIso` is the native
`isoSingleHomology`, and its homology normalization is stated explicitly.

These statements do not assert invertibility of the canonical module, an
original-map trace identity, Grauert--Riemenschneider vanishing, a uniform
bound, or resolution.
