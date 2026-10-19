# Polynomial and Laurent coefficient diagrams

[Laurent](Laurent/README.md) contains actual polynomial/Laurent coefficient maps and their natural under-category squares. These algebraic diagrams feed the corresponding spectrum and relative affine-space constructions.

The retained results are scalar-map identity/composition and evaluation/inversion naturality on the original algebras. They contain no curve-degree or K-theory application object.

`MonicIrreducible` supplies `Polynomial.MonicIrreducible` and finite support
for monic irreducible divisors of a nonzero field polynomial. It is independent
of Milnor K-theory; residue and power-series constant-closure consumers use
this same subtype and its irreducibility instance.

[RationalValues](RationalValues.lean) proves three facts about rational
polynomials used to re-index the flattening stratification by Hilbert polynomials
(Nitsure, arXiv:math/0504590v1, proof of Thm 4.3, pp. 22–23): two polynomials of
degree at most `n` that agree at `n + 1` consecutive integers are equal
(`Polynomial.eq_of_natDegree_le_of_eval_add_eq`); a polynomial is eventually
nonnegative or eventually negative on `ℕ`
(`Polynomial.eventually_nonneg_or_eventually_neg`); and one value `p ≥ N` orders
finitely many polynomials eventually (`Polynomial.exists_eval_le_imp_eventually_le`).
