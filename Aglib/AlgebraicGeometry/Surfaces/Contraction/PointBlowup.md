# Recognition of the original point blowup

`Scheme.Blowup.RegularPoint.isIso_lift_of_integral_closedFibre` identifies
the original proper modification of `Spec A` with the actual blowup of its
maximal ideal. The hypotheses are a commutative regular local ring `A` of
dimension two, an integral source, properness, an isomorphism over the original
centre complement, and an integral one-dimensional literal closed fibre.
The Cartier hypothesis is `cartierPullback`: local rank one of the actual
embedded inverse-image maximal ideal. The concluded isomorphism is the existing
`BlowupDatum.lift`, with its existing `lift_map` triangle.

The proof uses no exceptional-coordinate or conormal-frame compatibility.
There is no perfectness, excellence, separability, coefficient-field or
source-normality premise. Normality of the blowup is derived from its proved
regularity and general regular-local normality.

The module also gives a general normal-blowup criterion
`BlowupDatum.isIso_lift_of_curve_fibre`, whose source and target literal fibres
are integral curves. Its centre is Noetherian, and its source fibre may have
dimension at most one. The target-normality hypothesis in this general
criterion is discharged in the regular-local specialization.

The public `liftFibreMap` is the literal base-change arrow of the canonical
factor. Its two projection identities and `liftFibreMap_isPullback` keep the
original closed-fibre square. `lift_isProper`, `lift_restrict_isIso` and
`lift_isDominant` establish the factor properties from properness and the
common nonempty centre complement. Properness makes the factor surjective;
its actual closed-fibre map is then proper and dominant, hence finite by the
existing integral-curve theorem. The pullback-image identity gives finite
fibres on the exceptional divisor, and the complement isomorphism gives
singleton fibres elsewhere. The native proper quasi-finite theorem and
finite birational normal-target theorem identify the original factor.

The global theorem `RegularPoint.isIso_lift_of_integral_pointFibre` retains
an original closed immersion `c : Spec K ⟶ Y`, where `K` is the full original
field. The target is integral and locally Noetherian with regular stalks,
and its stalk at `c (closedPoint K)` has dimension two. Its remaining
hypotheses concern the original proper integral modification, the original
centre complement, the embedded inverse-image ideal, and the literal fibre
over `c`, with the same meanings as in the local theorem.

The canonical residue factor `Spec K ⟶ Spec κ(y)` is proved to be an
isomorphism: it is a surjective closed immersion into a reduced field
spectrum. Its factorization through `Y.fromSpecResidueField y` gives the
exact equality of the original centre ideals. Pasting the actual flat
stalk-blowup square with its local residue-fibre square supplies the global
exceptional fibre comparison. Thus the proof uses the original field and
point map without a chosen field identification or comparison premise.

`RegularPoint.isIso_lift_of_integral_pointFibre_of_normal` separates the
needed normality of the actual blowup from regularity of all target stalks.
It assumes regularity only at the original point, its local dimension two,
and `NormalStalks` of the actual blowup. The regular-target version derives
the last condition from `regularStalks_pointBlowup`.

`RegularPoint.isIso_lift_of_integral_pointFibre_of_regularLocal` removes
both global regularity of the target and global normality of its blowup.
Only the original point stalk is required to be regular local of dimension
two. The actual stalk comparison with the local point blowup proves
regularity at blowup points over that point. Elsewhere the canonical lift
is already an isomorphism. The finite birational criterion in
`Morphisms.Finite.Birational.NormalLocus` therefore applies with normality
only outside the isomorphism open. Singularities away from the centre are
allowed; no openness of the normal locus or excellence premise is used.

`BlowupDatum.isFinite_lift_of_curve_fibre` exposes the finiteness part of
the argument separately. It uses the original proper map, the common centre
complement, and the literal integral curve fibres, without a normality
hypothesis on the target blowup.

These are C5 recognition criteria. They do not establish the C4 contraction
construction, its target-stalk regularity, the identification of its
inverse-image point ideal, or the construction of a global contraction from
local models. Those remain the original consumers' obligations.
