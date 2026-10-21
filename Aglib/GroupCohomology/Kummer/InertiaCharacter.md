# Kummer and tame characters on actual inertia

`InertiaCharacter.lean` uses `GroupCohomology.Kummer` and preserves the source family's actual maps.

The actual Kummer cocycle restricts to a continuous character on the inertia subgroup of the
supplied prime in integralClosure R (AlgebraicClosure K). The level is positive and invertible
in R. The character initially requires only a commutative R-algebra field K. Under the stated
DVR and fraction-field hypotheses, its value is the integer fraction order times the
uniformizer character. The uniformizer character is independent of that choice. Root uniqueness
retains the nonzero residue hypothesis and needs no residue perfectness.

Source: `R5Lab.Aglib.GroupCohomology.Kummer.InertiaCharacter`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`949b2930214632e8320e70b03547f7df3b975b177ac9817003d795b92fdf83ab`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
