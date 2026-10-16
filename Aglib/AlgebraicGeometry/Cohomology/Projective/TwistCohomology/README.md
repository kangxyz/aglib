# Bounded flat Cech models of original projective twists

`Flat.lean` proves flatness for the unchanged native Cech model of every
integer twist over every commutative base ring. The coordinate and ring
universes remain the common geometric universe. Coordinates are finite,
and `e : ι ≃ Fin (n + 1)` specifies the bounded model's dimension.

`twistingCechComplex_free_X` identifies each original full-tuple Cech term
with its unchanged Laurent-coordinate module and uses the actual
`coordinateGradeEquivFinsupp` to prove freeness. The structural-ring action
is the original one induced by `ProjectiveSpace.toSpec` and `ΓSpecIso`.
`twistingCechIntComplex_flat_X` transports flatness through native zero
extension; all negative terms are the original zero objects.

`twistingFiniteCechComplex_flat_X` proves every term of
`moduleFiniteCechComplex` is flat. This is the existing good truncation of
the same integer Cech complex, strictly supported in `[0,n]`, with its
original inclusion into the full complex. Its boundary is the actual
cycle module. The proof uses the existing all-ring Cech comparison and
finite-cover bound to obtain universal tensor exactness at the next degree,
then applies the native flat-cycle/truncation theorem.

No Noetherianity, relative-flat coefficient assumption, or finite-projective
replacement is required. Full Cech terms may have infinite bases; this does
not assert finite-projective terms of the bounded model or K-flatness of
the unbounded full Cech complex. The bounded flat model is the input for
arbitrary-module tensor comparisons in relative projective Serre duality.
