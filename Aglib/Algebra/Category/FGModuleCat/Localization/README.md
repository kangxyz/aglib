# Localization of finite modules

The family extends the actual finite-module localization functor in
[`FGModuleCat/Localization.lean`](../Localization.lean), in the namespace
`ModuleCat.FiniteLocalization`.

[EssentialSurjectivity](EssentialSurjectivity.lean) descends finite generators over a
localized commutative ring. Essential surjectivity holds for an arbitrary commutative
coefficient ring and retains the actual localized-module comparison.

[Quotient](Quotient.lean) assumes a Noetherian coefficient ring for finite presentation,
scalar-denominator calculus and the torsion Serre quotient equivalence. Its scalar
morphism is the native linear-category expression `r • 𝟙 M`. Numerators and cancellation
retain this actual morphism, its localized underlying linear-map equation, and the
quotient factorization. The quotient functor is an equivalence with the category of finite
modules over the localized ring.
