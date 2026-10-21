# A vanishing neighbourhood from an extended actual fibre

Import `Aglib.AlgebraicGeometry.Cohomology.Proper.H0Vanishing.FieldExtension`.

`subsingleton_modulePointFiberCohomology_iff_fieldBaseChange` compares the
original ordinary point-fibre cohomology with its pullback along any field
extension of the same residue field. It works in every degree for a qcqs
morphism and quasicoherent coefficients. The point fibre, the further fibre
product and both coefficient pullbacks are literal native objects.

`exists_open_subsingleton_modulePointFiberH0_of_fieldBaseChange` applies
this reflection to a proper morphism over a locally Noetherian target, with
a finite-type quasicoherent relatively flat coefficient. Vanishing on an
extended fibre produces an actual open containing the original point, on
which every original ordinary fibre H⁰ vanishes. Taking that point to be
the generic point gives the open needed after finite-base spreading.

The result uses the existing
[proper H⁰ openness theorem](../H0Vanishing.lean) and the original canonical
[field-extension comparison](../../BaseChange/Modules/FieldExtension.md).
Recovery of a chosen external field fibre and coefficient is a separate
application of the given cartesian and module isomorphisms; those comparisons
are not replaced by an assumed vanishing-transport family.
