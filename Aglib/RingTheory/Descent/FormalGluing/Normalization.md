# Normalization under a supported conductor

Import `Aglib.RingTheory.Descent.FormalGluing.Normalization`.

Let `R → S` be a faithfully flat map of domains. The ambient commutative rings
`K` and `Q` are supplied with `IsFractionRing R K` and `IsFractionRing S Q`;
they are the original total quotient rings, hence fraction fields in this domain
case. No independent map or comparison of fraction fields is a premise.

For a finitely generated ideal `J ⊂ R`, assume an original nonzero element
`t ∈ J`, a ring equivalence `R/J ≃ S/JS` agreeing with the original coefficient
map on every element of `R`, and the literal conductor condition

```text
for s ∈ JS and b ∈ integralClosure S Q,
there is a ∈ S with algebraMap S (integralClosure S Q) a = s • b.
```

This last condition is exactly annihilation of the normalization quotient by
`JS`, expressed through its actual scalar inclusion. It is not finiteness of
the normalization or normality of an unspecified model.

`integralClosure.flatBaseChangeHom_surjective_of_conductor` proves
surjectivity of the existing `integralClosure.flatBaseChangeHom` from
`IntegralClosure.FlatBaseChange`. Together with that map's existing injectivity,
`flatBaseChangeHom_bijective_of_conductor` and
`flatBaseChangeEquivOfConductor` give the canonical algebra equivalence

```text
S ⊗[R] integralClosure R K ≃ₐ[S] integralClosure S Q.
```

Its pure-tensor theorem retains `flatFractionTensorMap R S K Q` on the original
ambient fraction value. Thus its forward map, multiplication, unit, and
structural coefficients are those already defined in the lower provider.
`finite_of_conductor_of_finite_upper` descends finiteness when the upper
normalization is finite. No Noetherian, complete, dimensional, Nagata,
excellence, or G-ring hypothesis occurs in these statements.

The proof reuses `FiniteModification`'s proved regular-conductor construction.
A finite generating family for `J` retains the actual `t` as a chosen
coordinate. Its cross-relation kernel and actual tensor comparison produce the
localization-intersection algebra `E ⊂ R[1/t]` and the original surjective map
`S⊗E → integralClosure S Q`. This invokes the existing proved finite-kernel
comparison; it does not assume one as a theorem-family input.

Each element of `E` maps to `K` through the original localization map. The
conductor equation identifies its fraction-tensor image with its actual image
in the upper normalization. The new helper
`Algebra.Descent.FormalGluing.isIntegral_of_one_tmul` descends integrality:
it constructs the original monogenic algebra, proves that its scalar extension
is finite using the integral tensor generator, and descends module finiteness
by faithful flatness. Therefore `E` maps into `integralClosure R K`. The actual
regular-conductor tensor map factors through `flatBaseChangeHom` on every
pure tensor, proving the required surjectivity.

The domain-normalization specialization uses monogenic integrality and the
original cross-relation argument above. Its conductor, faithful-flatness,
finiteness and fraction-field hypotheses remain explicit.

For the intended completion application set `J=(m_A C)^N` on each actual
ordinary blowup chart, and `t=a^N` for an original nonzero `a∈m_A`. The
completion quotient comparison, upper normalization finiteness, supported
defect bound, actual chart domains, scheme gluing, and finite-chain induction
remain consumer obligations. This module supplies none of the complete-local
resolution theorem or the upper sequence itself.
