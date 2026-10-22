# Artin approximation for geometric local Henselizations

Import [GeometricLocalArtinApproximation](GeometricLocalArtinApproximation.lean).
Let `k : Type u` be an arbitrary field, `B : Type v` a commutative finite-type
`k`-algebra, and `q : Ideal B` any prime. Put
`H = Henselization (Localization.AtPrime q)` using the actual Henselization
and prime localization. The coefficient and algebra universes are independent.

`GeometricLocalHenselization.exists_solution_ideal_completion_with_precision`
applies to every proper ideal `I` of `H`, finite variable and equation types
`σ` and `ι`, a system `F : ι → MvPolynomial σ H`, and a formal root
`y : σ → AdicCompletion I H` of that system. For every `c : ℕ`, it returns
`x : σ → H` satisfying every original equation and, for each variable `j`,
both precision statements:

```lean
Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)
algebraMap H (AdicCompletion I H) (x j) - y j ∈
  (I ^ c).map (algebraMap H (AdicCompletion I H))
```

The variable and equation universes are independent of each other and of
`u` and `v`. The statement includes `c = 0`. The finite-origin model, its solver
and the completion equivalence are constructed in the imported leaves;
separability and a coefficient-field section are not hypotheses.

## The finite-origin construction

[GeometricLocalFiniteOriginModel](GeometricLocalFiniteOriginModel.lean) gives
`GeometricLocalHenselization.exists_finite_origin_model`. It constructs a field
`K`, a natural number `n`, and a finite commutative local algebra `A` over
`Henselization (PolynomialLocalRing K n)`, together with an actual ring
equivalence `H ≃+* A`. Both `K` and `A` inhabit `Type (max u v)`, so the
existing [finite-local polynomial-origin solver](PolynomialLocalHenselizationFiniteLocalApproximation.lean)
applies in their common universe. No equality of the original `k` and `B`
universes is needed.

[ResidueParameterBasis](ResidueParameterBasis.lean) selects a transcendence basis
among the images of actual finite algebra generators in the prime quotient
`B ⧸ q` and lifts it to those same generators. The parameter polynomial ring
has zero contraction of `q`. [Fraction-base localization](../Localization/FractionBase.lean)
inverts its nonzero elements, supplies the rational-function coefficient field
action, and retains the selected prime, original prime localization and
quotient-map square. [ResidueParameterAnnihilator](ResidueParameterAnnihilator.lean)
uses that coefficient square to obtain actual monic positive-degree equations
for the residue coordinates; the basis need not be separating.

[MonicFiniteReduction](MonicFiniteReduction.lean) constructs a polynomial-algebra
action for which the original generators are integral and the algebra is
module-finite.
[MonicFiniteOriginModel](MonicFiniteOriginModel.lean) takes the selected local
factor of the actual tensor product with the polynomial-origin Henselization.
Its finite-local structure and ring equivalence use the original localization
and Henselization comparisons. The endpoint applies the finite-local solver
there, then [RingEquivApproximation](../AdicCompletion/RingEquivApproximation.lean)
returns the solution to the original `H`.
[AdicCompletion.congrRingEquiv](../AdicCompletion/RingEquiv.lean) carries the
finite quotient projections and extended ideal powers through that return,
which gives the two precision statements above in the original completion.

The theorem concerns these actual Henselizations of prime localizations of
finite-type algebras over a field. It does not replace `H` by an arbitrary
chosen Henselian ring. Approximation for arbitrary excellent Henselian local
rings and the general excellent-DVR Artin route remain outside its scope.
The earlier [polynomial-origin and finite-local interfaces](README.md)
retain their stated hypotheses and precision maps.
