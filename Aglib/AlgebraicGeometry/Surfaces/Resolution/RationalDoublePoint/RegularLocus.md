# Finite singular support on normal surface charts

Source: [RegularLocus.lean](RegularLocus.lean).

The topological helper decomposes a closed subset of a Noetherian sober
space into finitely many closed irreducible components. If every point of
the subset is closed, each component's generic point is closed, so that
component is a singleton.

For a Noetherian normal domain B of dimension at most two, the existing
normal codimension-one regularity theorem shows that every nonregular
prime is maximal. Thus an open regular locus has finite complement.
No semilocality assumption on B is used.

`finite_compl_regularLocus_of_finiteType_of_isJ2Ring` obtains this openness
from the original finite-type A-algebra structure and full J-2 for A.
`finite_compl_regularLocus_of_finiteType_complete_local` derives J-2 from
completeness, Noetherianity, locality and dimension at most two of A:
the existing complete-local Nagata theorem and semilocal Nagata J-2
criterion supply it. The auxiliary universe is zero, so the test algebras
are in the same universe as the base. B need not be local, semilocal,
complete, or finite as an A-module.

The dimension and normal-domain hypotheses on `B` remain explicit.
`FiniteSingularLocus` supplies the scheme-level consumer: it derives these
properties for the original affine rings and transports singular points
through the original spectrum-stalk and open-stalk isomorphisms.

Present consumers: [FiniteSingularLocus](FiniteSingularLocus.md).
