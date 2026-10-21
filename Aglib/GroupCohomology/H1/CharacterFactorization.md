# Factoring pointed characters through their actual cyclic image

`CharacterFactorization.lean` uses `GroupCohomology.PointedCohomology.CharacterFactorization` and preserves the source family's actual maps.

For arbitrary topological groups G and N with the stated action, a continuous equivariant
character into ZMod m factors uniquely through ZMod d when d is its actual additive order. The
level m is nonzero, d divides m, and the literal divisor insertion must be equivariant. N can
be infinite and noncommutative. The construction preserves the kernel, proves surjectivity of
the factor, and extends through the existing pointed-H1 equivalence. The zero character has
order one. Continuous coefficient actions are used only in the pointed-cohomology section.

Source: `R5Lab.Aglib.GroupCohomology.H1.CharacterFactorization`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c7ee112c42c14905a91e4a5fff8f6eaee99b95991981beb98aec53632133256d`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
