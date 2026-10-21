# Finite étale covers across nilpotent thickenings

[Nilpotent.lean](Nilpotent.lean) constructs finite étale cover lifts on an
arbitrary scheme across an actual nilpotent closed subscheme. The global
endpoints are `subscheme_baseChange_isEquivalence`, for
`I : X.IdealSheafData` with `IsNilpotent I`, and
`closedImmersion_baseChange_isEquivalence`, for the original closed immersion
`j : T ⟶ X` with `IsNilpotent j.ker`. Both concern the literal native
`Scheme.FiniteEtale.baseChange` functor.

No Noetherianity, properness, flatness, Henselianity or completeness is assumed.
The nilpotence condition is an actual global exponent; no claim for an
arbitrary closed immersion is made.

## Affine input

The affine input proves bijectivity of the actual Hom map and an equivalence
for the literal functor

```lean
Scheme.FiniteEtale.baseChange
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
```

The assumptions are only `CommRing R`, `I : Ideal R`, and `IsNilpotent I`.
The public endpoints are `quotient_baseChange_full`,
`quotient_baseChange_hom_bijective`, and
`quotient_baseChange_isEquivalence` in
`Scheme.FiniteEtale.Nilpotent`.

## Original arrows and objects

For a fixed formally étale `R`-algebra `A` and any `R`-algebra `B`, the actual
map

```text
(A →ₐ[R] B) → ((R/I) ⊗[R] A →ₐ[R/I] (R/I) ⊗[R] B)
```

is bijective. Its forward operation is `TensorProduct.map (AlgHom.id _ _)`.
To lift an arrow, restrict it to the original `A` factor, identify the target
tensor product with `B/IB`, and use formal smoothness to lift through the
nilpotent ideal `IB`. Formal unramifiedness gives uniqueness. Neither algebra
needs to be finite for this Hom argument.

The affine spectrum/tensor comparison converts this constructed algebra map
to the original scheme arrow. The proof retains the actual first pullback
projection equations. Essential surjectivity is the independently constructed
[affine object lift](ProperResidue/Existence.lean), whose
[ring provider](../../../RingTheory/Etale/NilpotentLift.lean) lifts a square
Jacobian presentation and finite generators. No Hom-lifting family,
object-lifting family or cover equivalence is an assumption.

The auxiliary uniqueness argument works after any surjective base change
through a formally unramified, locally finite-type target. Its open diagonal
equalizer contains the image of the surjective pullback projection, hence
is the whole source. This supplies uniqueness for future overlap cocycles
without assuming flatness of a nilpotent closed immersion.

## Constructing the global cover

Mathlib's original subscheme cover has charts
`Spec (Γ(X,U) / I.ideal U)` over each affine open `U` of `X`. Global nilpotence
implies nilpotence of each of these ring ideals. Their inclusion maps are
the quotient spectrum maps followed by the original affine-chart
isomorphisms. The subscheme-cover square and its open-range equation identify
these maps with the literal local pullbacks of `I.subschemeι`. Thus every
local equivalence used in the construction is proved from the affine input.

For a prescribed finite étale cover of the subscheme, choose its constructed
local lifts. Local fullness supplies their overlap arrows. The unramified
uniqueness argument proves identities, compositions and naturality of the
original structural maps. It does not assert that pullback is faithful on
the category of all schemes.

For each overlap, form the actual comparison from the source local cover to
the pullback of the target local cover. Its residue restriction is an
isomorphism. The native iterated-pullback comparison identifies this map with
the local finite étale base change, whose proved equivalence reflects
isomorphisms. The original comparison is therefore an isomorphism, proving
the transition square Cartesian.

Native relative gluing now constructs an actual finite étale scheme over
`X`. Pullback preserves the original open-cover colimit, so the local residue
comparisons give an isomorphism from its literal base change to the
prescribed cover. The arbitrary closed-immersion endpoint uses the native
image isomorphism internally and retains `baseChange j` in its conclusion.

`specMap_pullback_baseChange_isEquivalence` also handles a surjective ring map
`φ : R →+* S` with nilpotent kernel and an arbitrary original map
`π : X ⟶ Spec R`. Its functor is literally
`baseChange (pullback.fst π (Spec.map (CommRingCat.ofHom φ)))`.
The proof identifies the original spectrum kernel on global sections,
transports its nilpotence along the actual ideal pullback, and proves
nilpotence of the projection's kernel. That geometric nilpotence is a
conclusion of the proof, not a new premise.
`quotient_pullback_baseChange_isEquivalence` specializes to the original
quotient map of a nilpotent ideal of `R`.

## Boundary for proper models

The maximal-ideal closed fibre of a proper model over a DVR is generally not
a nilpotent thickening. The theorem applies instead to its finite-order
thickenings once their actual kernels are proved nilpotent. A compatible
tower over all orders still requires algebraization, and descent from an
incomplete Henselian base requires the applicable approximation and
finite-stage descent results. Those are separate suppliers; this file does
not prove proper-model essential surjectivity.
