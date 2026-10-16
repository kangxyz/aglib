# Exterior powers of scheme modules

`Restriction` specializes the sole generic module-sheaf exterior power to
`X.Modules`. Both `moduleExteriorPowerFunctor` and `moduleExteriorPower` are
definitionally the constructions in
`Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic`; there is no second
exterior object.

`moduleExteriorPowerOverIso` compares the exterior power of `M.over U` with
the original exterior sheaf restricted to the same open. It is built from
the identity on the original pointwise exterior modules and the existing
`PresheafOfModules.Restriction.sheafificationOverIso`. The forward and inverse
maps preserve the original wedges, and the comparison is natural for the
original coefficient morphisms. The proof also identifies the existing
restriction/sheafification comparison as the adjunct of the actual restricted
unit. These statements hold on every scheme, in every exterior degree,
including zero, without local freeness or any assumption on the base.

`LocallyFree` constructs the actual top exterior line from any displayed
`SheafHasRank M n`. `moduleExteriorTopOverIso` evaluates an original wedge
by the determinant of its coordinates in a given original free presentation.
`moduleExteriorTopGeneratorsData` retains both `q.I` and `q.X` definitionally;
the original local basis maps are reindexed to `ULift (Fin n)` and their
top wedges give singleton generators on those same opens. The resulting
`moduleExteriorTop_hasRank`, `moduleExteriorTop_isLocallyRankOne` and
`moduleExteriorTop_isFiniteLocallyFree` have no field, Noetherian, or
positive-rank premise. In particular, rank zero is included.

`moduleDeterminantLineBundle` places this same exterior sheaf in the existing
`Invertible.LineBundle X` type. It introduces neither a replacement sheaf
nor a new line-bundle property. Smooth canonical lines and the determinant
identifications in duality are subsequent consumers; this family does not
by itself identify a dualizing sheaf with a top differential exterior power.
