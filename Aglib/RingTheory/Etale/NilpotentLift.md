# Finite étale algebra existence across nilpotent ideals

[NilpotentLift.lean](NilpotentLift.lean) constructs an algebra over the original
base from a prescribed algebra over a nilpotent quotient. For a commutative
ring `R`, a nilpotent ideal `I`, and an étale `(R ⧸ I)`-algebra `B`,
`Algebra.Etale.exists_nilpotent_lift` produces an actual étale `R`-algebra `A`
and an isomorphism

```text
(R ⧸ I) ⊗[R] A ≃ₐ[R ⧸ I] B.
```

If `B` is finite as a module, `exists_finite_nilpotent_lift` produces `A`
finite as a module too. `exists_finite_nilpotent_quotient_lift` gives the
equivalent quotient formulation using the literal ideal
`I.map (algebraMap R A)` in the same constructed algebra. No Henselianity,
Noetherianity, completeness, finite generation of `I`, nontriviality or
monogenic presentation is assumed.

## Constructing the algebra

Mathlib's proved
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero` supplies a finite
submersive presentation `P` of `B` with dimension zero. Its generators and
relations may have arbitrary finite index sets. The presentation theorem
also covers the zero algebra.

Lift the coefficients of each relation along the surjection `R → R ⧸ I`.
Define `A` as the polynomial algebra over `R` modulo these lifted relations,
and let `Q` be its native naive presentation. Base changing `Q` gives the
original relations of `P`, so equality of the two relation ideals gives the
displayed algebra isomorphism. The proof records its action on the actual
polynomial evaluations.

The Jacobian of `Q` maps to the unit Jacobian of `P`. The extended ideal `IA`
is nilpotent. Units lift across a nilpotent quotient, so the Jacobian of `Q`
is itself a unit. Thus `Q` is submersive and has the original dimension zero,
which proves `Algebra.Etale R A`.

The quotient formulation composes the constructed tensor isomorphism with
`quotIdealMapEquivQuotTensor A I`. Its reduction map therefore sends an
original element `a : A` to the image of `1 ⊗ a` under that isomorphism.

## Finiteness without a Noetherian hypothesis

Choose finitely many lifts of module generators of the reduction. If `N` is
their span in `A`, then `N + IA = A`. For every natural number `m`, induction
gives `N + I^m A = A`: substitute the preceding equality into `I^m A` and
use `I^m N ⊆ N`. A nilpotence exponent makes the second summand zero, so
`N=A`. This does not assume finite generation of `A` before proving it.

The [affine scheme consumer](../../AlgebraicGeometry/Morphisms/FiniteEtale/ProperResidue/Existence.lean)
uses the actual tensor isomorphism to construct a pullback square for the
prescribed finite étale cover. The [global nilpotent equivalence](../../AlgebraicGeometry/Morphisms/FiniteEtale/Nilpotent.md)
constructs the corresponding scheme cover by gluing. Proper formal
algebraization remains a separate obligation.
