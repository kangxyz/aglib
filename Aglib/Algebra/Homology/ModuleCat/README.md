# Module cones and finite Laurent Čech models

[FiniteParametrix](FiniteParametrix.lean) constructs `ModuleCat.linearMapCone`
from the actual degree-zero single map. The source module and the right finite
defect module are projective; both defect modules are finite. The target
module need not be projective. The two supplied defect factorizations produce
an actual bounded finite-projective replacement and a homotopy equivalence.
No Noetherian hypothesis is added.

[LinearMapConeShift](LinearMapConeShift.lean) shifts the same cone by minus one
to degrees zero and one. Its source coordinate is negated to cancel the actual
shift sign, so the displayed differential is the original linear map.
[LinearMapConeIso](LinearMapConeIso.lean) transports these same cone and shifted
objects through specified commuting linear coordinate isomorphisms.

[LaurentProjectorCech](LaurentProjectorCech.lean) proves finite-projective models
for actual polynomial projector images with the displayed rectangular Laurent
transition equations. The finite cutoff bounds are proved in the lower Laurent
family. [LaurentModuleCech](LaurentModuleCech.lean) uses genuine finite-free
retractions to identify the signed module differential with those coordinates.
Its declarations belong to `ModuleCat.LaurentCech` and preserve the distinct
positive and negative scalar maps and the specified overlap isomorphism.

[FiniteHomology](FiniteHomology.lean) adds finiteness of actual homology over a
field and transport through a supplied homotopy equivalence. The actual first
homology of a two-term presentation is its signed cokernel. The Laurent
finite-projective model consequently gives finiteness of the original module
cokernel over a field. No geometric sheaf or projective-line identification is
an input to these module statements.
