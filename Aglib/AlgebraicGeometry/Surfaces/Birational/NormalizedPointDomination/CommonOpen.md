# A common open for two birational models

Source: [CommonOpen.lean](CommonOpen.lean).

Let `f : X ⟶ S` and `g : Y ⟶ S` be proper dominant maps of integral schemes,
with invertible original function-field maps. Assume `S` is Noetherian and
normal. `exists_commonOpen` constructs a nonempty quasi-compact open `U ⊆ X`
and an open immersion `h : U ⟶ Y` with `U.ι ≫ f = h ≫ g`.
Source normality and regularity are unnecessary.

The comparison uses the literal restriction of `f`, the inverse restriction
of `g`, and the second source-open inclusion on the intersection of their
target isomorphism neighborhoods. Properness over the Noetherian target gives
the source Noetherianity used for quasi-compactness.

Present consumers: [NormalCommonModel](NormalCommonModel.md).
