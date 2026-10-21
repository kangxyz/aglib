# Surjectivity of the actual uniformizer tame character

`TameSurjectivity.lean` uses `GroupCohomology.Kummer` and preserves the source family's actual maps.

The uniformizer Kummer character on actual inertia is surjective in characteristic zero at each
positive level invertible in the DVR R. The fraction field, supplied prime above the maximal
ideal, and chosen irreducible uniformizer are retained. The proof first derives divisibility of
exponents in a finite faithful formally unramified Dedekind R-algebra. Its normalization
argument requires every embedding of the root-generated field to be fixed by original inertia;
fixedness of the displayed root alone is propagated to that full quantifier before the
etaleness theorem is applied.

Source: `R5Lab.Aglib.GroupCohomology.Kummer.TameSurjectivity`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b8a7579e9f2a4d1de414c380930ab8bda48bba45fbffd93486c6a96d7fa53eaa`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
