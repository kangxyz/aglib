# Flat base change of the original normalization

`integralClosure.flatFractionTensorMap R S K Q` constructs the actual
S-algebra map S⊗[R]K→Q when R→S is flat, K is a supplied total quotient
ring of R, and Q is a supplied total quotient ring of S. The four rings
may have independent universes. The original coefficient actions are
retained. Domain, reducedness, locality, and completeness are not
hypotheses of this construction.

The native localization-after-base-change theorem identifies S⊗[R]K
as the localization of S at the images of the nonzerodivisors of R.
Flatness makes multiplication by each such image injective on S.
Its image in Q is therefore a unit, which verifies the unit condition
for the actual localization lift. The map extends S→Q and satisfies

```text
flatFractionTensorMap R S K Q (1 ⊗ algebraMap R K r)
  = algebraMap S Q (algebraMap R S r).
```

The localization injectivity criterion reduces injectivity of this map
to injectivity of the original S→Q total-quotient map.

`integralClosure.flatBaseChangeHom R S K Q` is the S-algebra map

```text
S ⊗[R] integralClosure R K →ₐ[S] integralClosure S Q.
```

It first tensors the original inclusion of the lower normalization
into K, then applies the fraction tensor map. The source is integral
over S by the native tensor-product integrality theorem, so mapping
the integral equations restricts the target to its literal normalization.
Flatness preserves injectivity of the original inclusion. The resulting
map is injective and retains the ambient value of each integral element:

```text
↑(flatBaseChangeHom R S K Q (s ⊗ x))
  = flatFractionTensorMap R S K Q (s ⊗ (x : K)).
```

`integralClosure.finite_of_faithfullyFlat R S K Q` assumes that R→S is
faithfully flat, S is Noetherian, and the literal upper normalization
is finite over S. The injective S-linear map above makes the scalar
extension of the original normalization finite over S. Native descent
of module finiteness under faithful flatness then gives finiteness of
`integralClosure R K` over R.

The current consumer is
[AdicCompletion/Normalization](../AdicCompletion/Normalization.lean).
It proves upper finiteness from the reduced complete-surface theorem
for the actual completion. This generic owner has no completion or
complete-surface dependency. The construction is the normalization
tensor argument used in [Stacks, Lemma 10.162.10 (032Y), proof of (4)](https://stacks.math.columbia.edu/tag/032Y).
