# Field trace through the original birational square

For the commuting square `π ≫ a = b ≫ s` of dominant morphisms of integral
schemes, assume the original function-field maps of `a` and `b` are
isomorphisms. `functionFieldTrace_birational_square` proves

```text
ff(a)(Tr_(K(T)/K(S))(z)) = Tr_(K(Y)/K(X))(ff(b)(z)).
```

Both scalar structures are induced by the original horizontal morphisms.
The two ring equivalences are those of the original vertical generic-stalk
maps. Their scalar square follows from `functionFieldMap_comp` and the
actual scheme square. The native `Algebra.trace_eq_of_equiv_equiv` then
gives the formula, without a chosen replacement identification or a supplied
trace-compatibility equation.

No finiteness, separability, normality, properness, or dimension hypothesis
is needed for this transport statement: the native algebra trace is defined
for these ring algebras. The surface consumer separately supplies the actual
finite field extension and its nonzero discriminant. It uses the formula on
products of the fixed original basis elements to identify its sheaf trace
Gram matrix with the pullback of the same base Gram matrix. The sheaf maps,
adjugate equations and H1 estimate remain separate constructions.
