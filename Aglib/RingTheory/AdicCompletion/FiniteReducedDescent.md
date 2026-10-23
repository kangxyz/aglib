# Reducedness descent through an actual completed finite algebra

Import `Aglib.RingTheory.AdicCompletion.FiniteReducedDescent`.

`AdicCompletion.isReduced_of_finite_of_completed_localizations R C`
assumes a Noetherian local ring R, a finite commutative R-algebra C,
and injectivity of its original algebra map. If the actual maximal-ideal
completion of C_q is reduced for every maximal ideal q of C, then the
actual maximal-ideal completion of R is reduced. Neither ring must be
a domain or normal, and C need not be local. There is no dimension or
branch-decomposition premise.

Write B for completion(R), and I for the original extended ideal m_R C.
The proof derives Noetherianity of C. It constructs the original residue
algebra R/m_R -> C/I using the canonical quotient map and the inclusion
of m_R in the contraction of I. The commuting scalar tower through R/m_R
is proved before finite generation over that residue field is used.
The actual C/I is therefore a finite residue-field algebra, hence
Artinian.

These are exactly the inputs of
[`exists_residueBranchesAlgEquiv`](FiniteLocalization.md). For each
q in MaximalSpectrum(C/I), the literal inverse image J_q in C is proved
maximal by surjectivity of the quotient map. The supplied reducedness of
the completed C_(J_q), and the existing `localizationAlgEquiv`, give
reducedness of the J_q-adic completion of C. The proved branch equivalence
then makes the I-adic completion of C reduced. No arbitrary product
isomorphism is supplied as a hypothesis.

The existing finite-algebra tensor comparison transfers reducedness to
`B ⊗[R] C`. The original injection R -> C supplies its faithful R-action.
Flatness of the actual completion B and
`Module.Flat.tensorProduct_mk_injective` prove injectivity of the actual
left tensor map B -> B tensor_R C. Reducedness descends along this map.

The underlying comparison is

```text
B -> B tensor_R C -> Completion_I C
  -> product_q Completion_(J_q) C
  -> product_q Completion_(maximalIdeal C_(J_q)) C_(J_q).
```

Its original coefficient maps are preserved. The tensor-to-completion
comparison sends 1 tensor c to the completion image of c. The C-algebra
branch equivalence retains each original coefficient and supplies the
exact quotient-factor evaluation at every level. The localization
completion equivalence sends that same coefficient to its actual local
image. The reducedness consumer uses the injection and these equivalences;
the branch supplier retains the more precise evaluation equation.

The current consumers are the dimension-at-most-one and dimension-at-most-
two Nagata analytic-unramifiedness arguments. There C will be the literal
finite normalization supplied by the Japanese property. Those consumers
must derive finiteness and injectivity of that original normalization map
and reducedness of its completed local branches. This module does not
assert those inputs, prove AU1/AU2, or supply the separate F2/CN2 theorem.

For the dimension bound in those later consumers, integral incomparability
suffices; normal-base going-down height equality is not assumed for an
initially nonnormal ring. The present descent theorem itself needs no
dimension argument.
