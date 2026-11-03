# Finite local scalar restriction and finite length

`ModuleCat.finiteLength_restrictScalars_of_finite_local` retains the literal
`ModuleCat.restrictScalars sigma` object for a finite local ring map
`sigma : R →+* A`. A module of finite A-length has finite R-length for that
same action. The coefficient rings are arbitrary commutative local rings;
Noetherianity, injectivity, surjectivity, completeness and dimension are not
assumed. The module universe remains independent of both ring universes.

The proof applies the native local-ring length restriction formula and the
finite residue degree supplied by the original finite local map. This is the
single body extracted from the chosen-embedding Grauert--Riemenschneider proof;
that consumer retains a thin private wrapper. It is distinct from restriction
along a surjective ring map in `FiniteLength/Restriction`.
