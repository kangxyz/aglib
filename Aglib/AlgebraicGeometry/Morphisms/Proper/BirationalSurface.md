# Actual proper birational restrictions on normal surfaces

`Hom.isIso_restrict_of_stalk_dimension_le_one` proves `IsIso (f ∣_ U)` for
an arbitrary actual target open U whose original Y-stalks have dimension
at most one. Its hypotheses are integral X and Y, locally Noetherian Y,
`NormalStalks Y`, properness and dominance of the original f, and
invertibility of its original `functionFieldMap f`.

The existing `Surfaces/Birational/IsomorphismLocus` owner supplies the
literal union of all isomorphism opens and proves that the original
restriction to that union is an isomorphism. Its valuation-ring theorem
places each normal point of stalk dimension at most one in that union,
including the field case. The new open-U adapter proves U is contained
in this existing locus, then uses native restriction and the original
double-restriction arrow isomorphism. It constructs no replacement map
or function-field identification.

## Local affine consumer

`ringKrullDim_stalk_le_one_of_ne_closedPoint A hdim p hp` proves the
required actual-stalk inequality for every p other than the closed point
of a local affine scheme, assuming `ringKrullDim A ≤ 2`. It does not need
normality, Noetherianity or integrality for this dimension assertion.
A nonclosed point has a strict specialization; finite coheight and the
dimension bound force coheight at most one. The native stalk/coheight
identity gives the desired inequality.

The GR cohomology caller already owns `localPuncturedSpectrum A`. It can
apply this pointwise lemma using `mem_localPuncturedSpectrum`, then pass
the resulting predicate to `Hom.isIso_restrict_of_stalk_dimension_le_one`.
This geometry file neither imports that cohomology owner nor duplicates
the punctured-spectrum definition.

## Finite closed complement

The existing theorem
`Hom.finite_compl_targetIsomorphismLocus_of_isProper_birational` is the
finite-set endpoint for a Noetherian normal integral target with
`topologicalKrullDim Y ≤ 2`. Its proof decomposes the closed complement
into finitely many irreducible closed sets and uses each generic point,
which is already closed, to identify each component with a singleton.
Thus Noetherianity and sobriety are both used. This endpoint is re-exported
through the import and is not duplicated here.

The new
`Hom.ringKrullDim_stalk_eq_two_of_not_mem_targetIsomorphismLocus` proves
that every remaining point has actual stalk dimension exactly two when
`SurfaceDimensionAtMostTwo Y` holds. A remaining point cannot have
coheight at most one; the bound at two therefore gives equality.
`codimensionTwoPointsClosed_of_dimension` then also supplies its closedness.
The complement itself is closed because the original locus is open.

No regularity assumption on X, Nagata or excellence assumption, J-2
hypothesis, catenary formula, absolute separatedness or regular-locus
openness is used. Properness supplies the relative separatedness in the
existing valuation-ring neighbourhood theorem. The two current consumers
are the proper finite-length H1 argument on a local normal surface and
the finite bad-set step for a supplied proper birational regular model.
