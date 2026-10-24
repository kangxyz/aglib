# The actual normalization of the ordinary rational surface blowup

This module supplies the normalization, dimension, cohomology and original
ideal-pullback part of the ordinary rational-blowup argument. It uses the
existing honest `NormalModificationH1Vanishing A` predicate. That predicate
quantifies over actual normal proper birational models; it does not supply
a resolution or assume normality of the ordinary blowup.

The original base is a commutative local domain `A` of dimension two.
Noetherianity and the given Nagata property are used to derive finiteness
of the actual normalization and coherent vanishing. Normality of `A` is
used for the actual global coefficient bijections. Universal rationality
is used only for structure-H1 and its finite-row consequences.

`MaximalIdealBlowup.datum` is the literal ordinary blowup of the full
maximal-ideal centre. `source` and `map` retain its source and blowdown.
The dimension witness excludes the local closed point from the generic
point, so the actual blowup is integral, dominant and birational. Properness
and local Noetherianity come from the existing ordinary blowup providers.

`gamma` is that source's original generic-point inclusion. `normalization`
and `nu` are exactly the native normalization and its original arrow for
`gamma`. The map `q` is the original composite `nu ≫ map`.

For each nonempty original affine open U, the proof uses the actual scalar
map obtained from `appLE` and the original spectrum section isomorphism.
Its germ square is the original function-field-map square. Birationality
writes an actual chart element as a/s in that original field, so the
nonzero polynomial sT−a proves algebraicity for exactly this scalar
map. Finite type and injectivity are obtained from the original morphism.
The finite-type Nagata surface theorem then supplies both Nagata and
dimension at most two on these actual chart rings.

`nu_isFinite` applies this to the original ordinary blowup and constructs
the finiteness of its literal normalization. `q_isProper` and
`q_fieldMap_isIso` keep the original composite and its function-field map.
Applying the same actual-chart argument to q and an original affine open
cover gives `normalization_dimension_le_two`. Thus
`closedFibre_dimension_le_one` derives the dimension bound on the full
actual maximal-ideal thickening. No projectivity of the normalization or
completeness of the base is used.

`normalization_structureH1` applies the honest universal rationality
predicate to this constructed normal proper birational model.
`normalization_coherent_higher_vanishing` uses the proved local proper
cohomological-dimension theorem to kill the original coherent cohomology
in every degree greater than one. Its `isZero` form retains the original
structural A-action. `normalization_finiteRow_H1` takes an actual finite
epimorphic row of global sections of an actual coherent module. It derives
coherence of the row kernel, H1 vanishing of the finite free source and
H2 vanishing of the kernel, then applies the original long exact sequence.
It does not assume kernel acyclicity or a global-generation conclusion.

`ordinaryCoefficients` and `coefficients` are the literal structural ring
maps from A to the ordinary and normalized global sections. Their bijection
theorems use normality of the original base. The ordinary comparison does
not assume that the ordinary blowup is normal.

`exceptionalIdeal` is the original full maximal-ideal image on the ordinary
blowup. `normalizedExceptionalIdeal` is its literal inverse image under nu;
the module proves that this is the same full centre pulled back along q.
The original map between its subschemes forms the full Cartesian centre
square. Generic-point avoidance, rather than a flatness hypothesis on nu,
makes the canonical `Hom.idealPullbackMap` an isomorphism. Its actual ideal
inclusion formula is retained, and invertibility of the normalized image
ideal follows. Proper dominance proves that its support is nonempty.

The source route is [Stacks 54.9.2, 0B4X](https://stacks.math.columbia.edu/tag/0B4X),
[54.9.3, 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y), and
[54.9.4, 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z). This module
supplies their normalization and ideal-pullback inputs.

[IdealPowers](Blowup/IdealPowers.md) constructs finite rows for the image
ideal and its powers, the cross-relations and the original section-image
induction. [Normality](Blowup/Normality.md) matches the tautological
embedding and uses positive-twist H1 vanishing and coherent cokernel
generation to descend normality. [Exceptional](Blowup/Exceptional.md) and
[Powers](Blowup/Exceptional/Powers.md) give the exceptional-fibre section
quotients and their H1 vanishing through the original quotient/product
sequences. These results are derived by those modules; none is an input
to the normalization construction here. No Gorensteinness, regular source,
coefficient field, trait or resolution is assumed.
