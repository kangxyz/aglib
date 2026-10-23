# Completion of an original localization of a finite algebra

Let `B` be a commutative Noetherian local ring and `C` a finite commutative
B-algebra. Let `p : Ideal C` be prime, with the exact contraction equation
`p.comap (algebraMap B C) = IsLocalRing.maximalIdeal B`. The localization is
literally `Localization.AtPrime p`, with its original canonical B-map.
The algebra providers used here place B and C in one universe `Type u`.

`AdicCompletion.FiniteLocalization.isLocalHom p hp` derives localness of that
original map. `completionMap p hp` extends it from
`AdicCompletion (maximalIdeal B) B` to
`AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)`.
`componentMap p hp n` is the actual induced quotient algebra map.
For every n, `eval_completionMap` is exactly the map

```text
B / (maximalIdeal B)^n  →  C_p / (maximalIdeal C_p)^n
```

induced by the original B→C_p. `maximalPower_le_comap` supplies the original ideal-power containment used in
each quotient map. The precision is the same n, and
`completionMap_algebraMap` preserves every original B-element.
`baseAlgebra p hp` is the corresponding explicit completed-base algebra value;
it is not supplied as a compatibility assumption or installed globally.

With `[IsNoetherianRing B]` and `[Module.Finite B C]`, the theorem
`FiniteLocalization.finite p hp` proves module finiteness of the actual target
completion over the original base completion, under exactly `baseAlgebra p hp`.
The map and localness suppliers do not require either finiteness or
Noetherianity; the full finiteness proof derives the necessary properties.

The original extended ideal is `I = (maximalIdeal B).map (algebraMap B C)`.
The finite residue algebra C/I over B/maximalIdeal B is Artinian. Its finite
maximal spectrum supplies the actual maximal ideals of C above I, by inverse
image along the original quotient map. Their product equals `I.radical`.
Noetherianity of C follows from finiteness over B and gives an actual positive
power of this radical contained in I. The cofinal comparison is constructed
from original quotient transition maps. The existing compatible finite CRT
comparison then splits the I-completion into all those actual ideal-adic
branches. No product-isomorphism or factorization oracle is assumed.

The selected prime p is proved maximal by integrality of the original finite
algebra. Its branch occurs in the residue spectrum, and the existing native
maximal-localization quotient comparisons identify its completion with the
original completed C_p. Thus the completion of C at I surjects onto this
actual completed local ring. The existing finite-algebra tensor comparison
makes the target a quotient of the finite B-completion module
`AdicCompletion (maximalIdeal B) B ⊗[B] C`. Compatibility with `completionMap`
is proved at every actual quotient component, so finiteness uses the same
canonical completed-base scalar action.

The general intermediate theorem `AdicCompletion.reindex_to_maximal_surjective`
works for a Noetherian ring A, an ideal I with Artinian A/I, and an original
maximal p containing I. It proves surjectivity of the literal quotient-system
map from the I-completion to the p-completion. This theorem supplies the
branch rather than taking a decomposition as a premise.

`AdicCompletion.exists_residueBranchesAlgEquiv I` makes the full comparison
available under the same Noetherian-A and Artinian-A/I hypotheses. It supplies
an A-algebra equivalence from `AdicCompletion I A` to the product indexed by
`q : MaximalSpectrum (A ⧸ I)`, with each literal branch ideal
`q.asIdeal.comap (Ideal.Quotient.mk I)`. For every level n, input x, and branch q,
evaluation of the q-component is exactly the quotient factor map induced by
`I^n ≤ (q.asIdeal.comap (Ideal.Quotient.mk I))^n`, applied to `evalₐ I n x`.
This includes level zero and retains the original quotient-system maps.
The existence theorem reuses the existing private construction and evaluation
proof; it exposes no private branch definitions or additional cofinality
premises. Its current consumer is the full semilocal completion comparison
in the Nagata analytic-unramifiedness argument, followed by the existing
maximal-localization completion equivalences.

The uncompleted ring C_p is not assumed finite over B. Neither ring must be a
domain. No flatness, free rank, coefficient field, separability, nonzero ideal
or discriminant hypothesis is needed. The result gives no full-cover degree
or normalized trace on individual completed factors, and it proves no
regularity, H¹ bound or resolution termination.
