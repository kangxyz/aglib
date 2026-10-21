# Height-one ideals with factorial ambient stalks

[Factorial.lean](Factorial.lean) proves
`Scheme.Hom.idealModule_isLocallyRankOne_of_factorialStalks` for an actual closed
immersion `i : C ⟶ X`, with locally Noetherian `X` and integral `C`. Its remaining
hypotheses are native pointwise statements about the actual ambient stalks:

```text
∀ x : X, IsDomain (X.presheaf.stalk x)
∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)
∀ c : C, (RingHom.ker (i.stalkMap c).hom).height = 1.
```

The conclusion is `IsLocallyRankOne X (Scheme.Hom.idealModule i)`, with no
dimension bound. No separate locally factorial scheme class is introduced.

Integrality of `C` makes each actual source stalk a domain, so each actual
stalk-map kernel is prime. The pinned Mathlib theorem
`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one` in
`Mathlib.RingTheory.Ideal.UFD` makes this height-one prime principal.
Height one makes it nonzero; its generator is therefore nonzero in the assumed
ambient domain and acts injectively on that ring. The existing
`Ideal.regularPrincipalIdealBasis` supplies a singleton basis of the actual
ideal module.

These pointwise bases feed the shared
[stalk-kernel criterion](StalkKernel.lean). That single implementation performs
the canonical germ comparison, finite-presentation basis spreading,
outside-image unit-ideal argument, and affine/restriction transport.
The height-one premise is retained explicitly. Regular schemes become a further
consumer after the separate regular-local unique-factorization theorem is
supplied; this factorial-stalk theorem does not assume a global Cartier family.
