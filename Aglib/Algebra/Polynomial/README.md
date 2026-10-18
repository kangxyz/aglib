# Polynomial and Laurent coefficient diagrams

[Laurent](Laurent/README.md) contains actual polynomial/Laurent coefficient maps and their natural under-category squares. These algebraic diagrams feed the corresponding spectrum and relative affine-space constructions.

The retained results are scalar-map identity/composition and evaluation/inversion naturality on the original algebras. They contain no curve-degree or K-theory application object.

`MonicIrreducible` supplies `Polynomial.MonicIrreducible` and finite support
for monic irreducible divisors of a nonzero field polynomial. It is independent
of Milnor K-theory; residue and power-series constant-closure consumers use
this same subtype and its irreducibility instance.
