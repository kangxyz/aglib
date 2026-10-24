# Fixed-target line-bundle root pairs

For a line bundle `L` on `X` and any `n : ℕ`, `Pair L n` stores an actual line
bundle `M` and the specified isomorphism
`(tensorPowerLineBundle X M n).val ≅ L.val`. `Iso P Q` stores an actual bundle
isomorphism and the exact equation relating the two specified power maps. The
Picard-class identity is a consequence of this data, not a replacement for it.

## Original maps and transport

[Basic](Basic.lean) supplies identity, composition, inverse and target transport
for root-pair isomorphisms. [Transport](Transport.lean) transports along an
actual bundle isomorphism and records `pullbackIdIso` and `pullbackCompIso`
using the native module-pullback identity and composition comparisons.
`Pair.pullback` uses the original power pullback comparison and the pullback of
the specified power map; it retains the target compatibility equation.

[Scalars](Scalars.lean) identifies automorphisms of an actual line bundle with
original global units via tensoring by its dual and the actual evaluation
equivalence. [ScalarPullback](ScalarPullback.lean) proves the scalar map formula
through the original pullback and its unit map. [Errors](Errors.lean) defines
`powerError`; equality with the identity is equivalent to the original root-pair
compatibility equation, and scalar precomposition changes the error by the
displayed `n`th power.

## Affine square-zero lifting

[Affine](Affine.lean) proves `exists_pair_lift_affine_of_square_zero` for
affine `X₀` and `X`, an original closed immersion `i : X₀ ⟶ X` with
`i.ker ^ 2 = ⊥`, any target line bundle `L`, any natural `n`, and any supplied
pair over `pullbackLineBundle i L`. It returns a pair over the same fixed `L`
and an actual root-pair isomorphism from its original pullback to the supplied
pair. This object-lifting statement needs no invertibility condition on `n`.

[SquareZeroUnits](SquareZeroUnits.lean) takes an arbitrary ring map with
square-zero kernel and `IsUnit (n : R)` to produce an actual principal `n`th
root of a principal unit; the ring map need not be surjective.
[SquareZeroIso](SquareZeroIso.lean) uses this correction to lift a *given*
root-pair isomorphism. Its additional premise is exactly
`IsUnit (n : Γ(X, ⊤))`; the conclusion identifies the bundle-isomorphism
component after original pullback. This prescribed-isomorphism statement
retains the invertibility premise.

## Review scope and provenance

The exact eight-source fixed-target square-zero cut received ordinary ACCEPT
for the statements and conditions recorded by its review. Its target manifest
SHA-256 is
`deb3d6469ca09999e3513675de3954c6bbeb8bb29ba2cd076451077ce2cfcfdc`; its
review source-manifest SHA-256 is
`c7e15ca5eef82029fe5a1efc1071299a5eef0fb8a00f40651a08815cbc80fcec`. The
integration packet retains each source hash and successful leaf-run locator
(packet manifest SHA-256
`4bcd68942cb8b6cf1d759651462f437a320cf61cb6650640a5a2eceaa96d476a`). This
cut does not assert global root existence, geometric uniqueness, groupoid
equivalence, nonaffine gluing, higher-nilpotence or formal lifting, or
henselian/global root conclusions.
