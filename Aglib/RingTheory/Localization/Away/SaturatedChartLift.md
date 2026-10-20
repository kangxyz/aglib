# Unique lifts from the actual saturated chart

This is a new proof on the existing object
`Localization.Away.saturatedChart A I (a : A)`, the generated subalgebra
of the actual localization `Localization.Away (a : A)`.

For arbitrary commutative rings `A` and `S`, an ideal `I`, a distinguished
`a : I` and an actual `f : A →+* S`, the inputs are:

- `IsRegular (f a)`;
- `∀ b : I, f a ∣ f b`.

`Localization.Away.SaturatedChart.liftOfHom` constructs the actual algebra
map with target algebra structure exactly `f.toAlgebra`.
`existsUnique_algHomOfHom` packages existence, uniqueness and the original
fraction equations in that same algebra-map type. `ringLift` is the
underlying ring map. The coefficient triangle is `g.comp (algebraMap A _) = f`,
and `existsUnique_ringHom` proves uniqueness with that exact triangle.
`liftOfHom_fraction_eq` identifies the original `b/a` with any `q : S`
satisfying `f a * q = f b`; regularity makes this quotient unique.

The construction maps the original localization into `S[1/f(a)]`.
Regularity makes the scalar map from `S` injective. Divisibility puts the
chart generators in its range; the actual adjoin closure does the same for
the entire chart. The inverse of the canonical range embedding supplies
the lift. `ringLift_localizationTriangle` retains this exact diagram.

There is no Noetherian, domain or nontriviality hypothesis. Regularity is
injectivity of multiplication, and is equivalent here to membership in
`nonZeroDivisors S`. Zero, nilpotent and zero-ideal cases retain these same
conditions. The focused client checks a genuine integer quotient, the zero
chart over a trivial target, and the nilpotent/regular boundary.

This supplies an affine chart lift. Scheme-level gluing, the full affine
blowup universal property and construction of a `BlowupDatum` remain separate.
