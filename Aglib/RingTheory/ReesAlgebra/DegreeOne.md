# Degree-one generation of the original Rees algebra

[DegreeOne.lean](DegreeOne.lean), in `reesAlgebra`, proves

    (grading I 1)^n = grading I n

for the native Rees subalgebra of the original polynomial ring and every
natural number `n`. The degree-zero case is included. The proof uses the
original homogeneous monomial and coefficient maps, with induction on
the actual powers of the original ideal.

`baseChange_grading_one_pow` proves the same equations for Mathlib's
grading on the full tensor algebra `S ⊗_R reesAlgebra I`. Private helpers
show that scalar extension of submodules preserves their products and
powers. No flatness, domain, nonzero or Noetherian hypothesis is required.
The scalar-extended Rees algebra is not replaced by its image in `S[t]`.

The current consumer is the degreewise-surjective polynomial presentation
used in the projective embedding of a base-changed blowup. These power
equations supply the generation hypothesis of
`AlgebraicGeometry.Proj.DegreeOneEmbedding`; an actual family spanning
degree one is supplied separately by the original coherent presentation.
No projectivity, closed immersion or geometric comparison is assumed by
this algebraic leaf.
