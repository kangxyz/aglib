# Actual conductor torsion and compatible quotient algebras

`FiniteModification.Torsion` imports the regular-conductor construction from
[FiniteModification](../FiniteModification.md). It treats the original
conductor torsion ideal, its actual quotient, native Artin–Rees separation,
and the algebra of compatible quotient pairs. All declarations remain in
`Algebra.Descent.FormalGluing`.

## The actual torsion ideal and compatible quotient pairs

For a commutative `S`-algebra `D`, `conductorTorsionIdeal t` is the actual
ideal `Ann_D(t)`, defined as the kernel of multiplication by the original
image of `t`. Assume the original `S→D` is injective and `t` is regular on
`S`. Its intersection with the original scalar image is zero. If also
`tD⊂S`, `conductor_double_torsion` proves `t²z=0→tz=0`: the element `tz`
is an original scalar, and regularity on `S` forces it to vanish.
Consequently `conductorTorsionQuotient_algebraMap_injective` and
`conductorTorsionQuotient_regular` give injection `S→D/Ann_D(t)` and
regularity of the same `t` on that actual quotient. No stabilization of an
unspecified annihilator chain is assumed.

An actual conductor ideal `J⊂S`, with `JD⊂S`, annihilates `Ann_D(t)` by
`conductor_smul_torsion_eq_bot`. The original conductor products also pass
to the actual quotient. For Noetherian `S` and finite `D`, when `J=I^n`,
`exists_pow_map_inf_conductorTorsion_eq_bot` applies the existing native
Artin–Rees separation theorem. It gives an actual ideal
`K=(I^m).map (algebraMap S D)` with `K∩Ann_D(t)=0`. No Jacobson-ideal or
adic separatedness hypothesis is used.

For any actual ideals `T,K⊂D`, `quotientFibreProduct T K` is the equalizer
subalgebra of `(D/T)×(D/K)` for the two original quotient maps into
`D/(T+K)`. `quotientDiagonal` is the pair of original quotient maps from
`D`. It is always surjective: a compatible pair represented by `a,b`
satisfies `a−b=u+v`, with `u∈T`, `v∈K`, and lifts through `a−u`.
It is injective when `T∩K=0`. `quotientFibreProductEquiv` packages this
actual algebra isomorphism and preserves the original scalar structure
and both original quotient maps. No comaximality assumption occurs.

The actual quotient comparisons are a supplier for the reviewed general C2
construction. The final scalar-extension assembly must still combine the
regular-conductor model of `D/Ann(t)` with the bounded-torsion counits of
`D/K` and `D/(Ann(t)+K)`. It must retain their two original quotient maps and
prove that the resulting tensor equivalence preserves the original scalar
map and punctured localizations. This module does not assume such a model,
a coaction, or the desired final equivalence as an input.

Mathematical basis: the independently reviewed C2 effectivity construction,
Sections 6–7, with the actual scalar and quotient maps. The broader classical
source is [Stacks Lemma 15.91.17, 0ALK](https://stacks.math.columbia.edu/tag/0ALK);
this module implements the explicit torsion reduction and quotient comparison
used in that fixed route, not the entire general gluing equivalence. No proper
scheme or Grothendieck-existence premise is involved.
