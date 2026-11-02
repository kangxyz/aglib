# First-power exceptional cohomology

Import:
`Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Exceptional.FirstPower`.

The input is the original commutative Noetherian normal Nagata local domain A
of dimension two, with genuine `NormalModificationH1Vanishing A`. The scheme E
is the full exceptional fibre of the actual ordinary maximal-ideal blowup;
L is its original positive line `exceptionalLine A hd`, and its cohomology
uses the original structure map `exceptionalStructureMap A hd` over A/m.

`exceptionalLineCohomologyCotangentEquiv` composes the existing degree-one
`exceptionalPowerTheta`, actual H0-section equivalence, native first-power
line comparison, and `exceptionalPowerOneCotangentEquiv`. Its target is the
native cotangent space with its original residue action. It does not choose a
coefficient-field section, change cohomology realization, or replace E by a
reduction. This is a comparison through existing maps, not another power-row
or quotient-section proof.

`exceptionalLine_h0_finrank_ge_three_of_not_regular` adds exactly nonregularity
of A. The native regular-local-ring criterion rules out at most two maximal-
ideal generators, and the native cotangent-rank identity gives the bound.
No three-generation or rank-exactly-three assumption is needed.

This lower numerical input supports actual exceptional-curve generation over
the original residue field, but does not prove that generation. There is no
canonical line, Gorenstein, inverse-line H1, full Hilbert function or generation
premise. It imports neither RDP consumers nor canonical curve duality. The
existing structural-H0 theorem is not needed here and is not exposed/copied.

## Verification

Native graph129 accepted production source `cbf14d3a` in 21 seconds at the
normal settings. Its result telescope explicitly retains the existing native
structural cohomology action. The numerical threshold uses the native
span-rank quotient theorem over the literal original residue quotient, not an
unproved identification of separately displayed finrank expressions. The
original Theta1/H0/right-unit comparison, hypotheses and scalar map are
unchanged. This result does not prove curve generation or canonical epimorphy.
